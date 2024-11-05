#include "dlinear/symbolic/symbolic_expression_cell.h"

#include <algorithm>
#include <cassert>
#include <cmath>
#include <functional>
#include <iomanip>
#include <limits>
#include <map>
#include <numeric>
#include <ostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>

#include "dlinear/symbolic/hash.h"
#include "dlinear/symbolic/symbolic_environment.h"
#include "dlinear/symbolic/symbolic_expression.h"
#include "dlinear/symbolic/symbolic_expression_visitor.h"
#include "dlinear/symbolic/symbolic_variable.h"
#include "dlinear/symbolic/symbolic_variables.h"
#include "dlinear/util/error.h"

namespace dlinear::drake::symbolic {

using std::accumulate;
using std::all_of;
using std::domain_error;
using std::endl;
using std::equal;
using std::hash;
using std::lexicographical_compare;
using std::map;
using std::numeric_limits;
using std::ostream;
using std::ostringstream;
using std::pair;
using std::runtime_error;
using std::setprecision;
using std::string;

namespace {
std::string mpq_to_string(const mpq_class &value) {
  if (value == 0) return "0";

  std::string ret;
  if (value < 0) ret += "(- ";
  if (value.get_den() == 1) {
    ret += std::to_string(std::abs(value.get_num().get_si()));
  } else {
    ret += std::to_string(std::abs(value.get_d()));
  }
  if (value < 0) ret += ")";
  return ret;
}

bool is_integer(const mpq_class &v) {
  // v should be in [int_min, int_max].
  if (!((numeric_limits<int>::lowest() <= v) && (v <= numeric_limits<int>::max()))) {
    return false;
  }

  mpz_class f{v};
  return v == f;
}

bool is_non_negative_integer(const mpq_class &v) { return (v >= 0) && is_integer(v); }

// Determines if the summation represented by term_to_coeff_map is
// polynomial-convertible or not. This function is used in the
// constructor of ExpressionAdd.
bool determine_polynomial(const std::map<Expression, mpq_class> &term_to_coeff_map) {
  return all_of(term_to_coeff_map.begin(), term_to_coeff_map.end(),
                [](const pair<const Expression, mpq_class> &p) { return p.first.is_polynomial(); });
}

// Determines if the summation represented by term_to_coeff_map includes an ITE
// expression or not. This function is used in the constructor of ExpressionAdd.
bool determine_include_ite(const std::map<Expression, mpq_class> &term_to_coeff_map) {
  return any_of(term_to_coeff_map.begin(), term_to_coeff_map.end(),
                [](const pair<const Expression, mpq_class> &p) { return p.first.include_ite(); });
}

// Determines if the product represented by term_to_coeff_map is
// polynomial-convertible or not. This function is used in the
// constructor of ExpressionMul.
bool determine_polynomial(const std::map<Expression, Expression> &base_to_exponent_map) {
  return all_of(base_to_exponent_map.begin(), base_to_exponent_map.end(),
                [](const pair<const Expression, Expression> &p) {
                  // For each base^exponent, it has to satisfy the following
                  // conditions:
                  //     - base is polynomial-convertible.
                  //     - exponent is a non-negative integer.
                  const Expression &base{p.first};
                  const Expression &exponent{p.second};
                  if (!base.is_polynomial() || !is_constant(exponent)) {
                    return false;
                  }
                  const mpq_class &e{get_constant_value(exponent)};
                  return is_non_negative_integer(e);
                });
}

// Determines if the product represented by term_to_coeff_map includes
// an ITE expression or not. This function is used in the constructor
// of ExpressionMul.
bool determine_include_ite(const std::map<Expression, Expression> &base_to_exponent_map) {
  return any_of(base_to_exponent_map.begin(), base_to_exponent_map.end(),
                [](const pair<const Expression, Expression> &p) {
                  const Expression &base{p.first};
                  const Expression &exponent{p.second};
                  return base.include_ite() || exponent.include_ite();
                });
}

// Determines if pow(base, exponent) is polynomial-convertible or not. This
// function is used in constructor of ExpressionPow.
bool determine_polynomial(const Expression &base, const Expression &exponent) {
  // base ^ exponent is polynomial-convertible if the followings hold:
  //    - base is polynomial-convertible.
  //    - exponent is a non-negative integer.
  if (!(base.is_polynomial() && is_constant(exponent))) {
    return false;
  }
  const mpq_class &e{get_constant_value(exponent)};
  return is_non_negative_integer(e);
}

Expression ExpandMultiplication(const Expression &e1, const Expression &e2, const Expression &e3);

// Helper function expanding (e1 * e2). It assumes that both of e1 and e2 are
// already expanded.
Expression ExpandMultiplication(const Expression &e1, const Expression &e2) {
  // Precondition: e1 and e2 are already expanded.
  assert(e1.EqualTo(e1.Expand()));
  assert(e2.EqualTo(e2.Expand()));

  if (is_addition(e1)) {
    //   (c0 + c1 * e_{1,1} + ... + c_n * e_{1, n}) * e2
    // = c0 * e2 + c1 * e_{1,1} * e2 + ... + c_n * e_{1,n} * e2
    const mpq_class &c0{get_constant_in_addition(e1)};
    Expression ret{ExpandMultiplication(c0, e2)};
    for (const auto &p : get_expr_to_coeff_map_in_addition(e1)) {
      const Expression &e_1_i{p.first};
      const mpq_class &c_i{p.second};
      ret += ExpandMultiplication(c_i, e_1_i, e2);
    }
    return ret;
  }
  if (is_addition(e2)) {
    //   e1 * (c0 + c1 * e_{2,1} + ... + c_n * e_{2, n})
    // = e1 * c0 + e1 * c1 * e_{2,1} + ... + e1 * c_n * e_{2,n}
    const mpq_class &c0{get_constant_in_addition(e2)};
    Expression ret{ExpandMultiplication(e1, c0)};
    for (const auto &p : get_expr_to_coeff_map_in_addition(e2)) {
      const Expression &e_2_i{p.first};
      const mpq_class &c_i{p.second};
      ret += ExpandMultiplication(e1, c_i, e_2_i);
    }
    return ret;
  }
  return e1 * e2;
}

Expression ExpandMultiplication(const Expression &e1, const Expression &e2, const Expression &e3) {
  return ExpandMultiplication(ExpandMultiplication(e1, e2), e3);
}

// Helper function expanding pow(base, n). It assumes that base is expanded.
Expression ExpandPow(const Expression &base, const int n) {
  // Precondition: base is already expanded.
  assert(base.EqualTo(base.Expand()));
  assert(n >= 1);
  if (n == 1) {
    return base;
  }
  const Expression pow_half{ExpandPow(base, n / 2)};
  if (n % 2 == 1) {
    // pow(base, n) = base * pow(base, n / 2) * pow(base, n / 2)
    return ExpandMultiplication(base, pow_half, pow_half);
  }
  // pow(base, n) = pow(base, n / 2) * pow(base, n / 2)
  return ExpandMultiplication(pow_half, pow_half);
}

// Helper function expanding pow(base, exponent). It assumes that both of base
// and exponent are already expanded.
Expression ExpandPow(const Expression &base, const Expression &exponent) {
  // Precondition: base and exponent are already expanded.
  assert(base.EqualTo(base.Expand()));
  assert(exponent.EqualTo(exponent.Expand()));
  // Expand if
  //     1) base is an addition expression and
  //     2) exponent is a positive integer.
  if (!is_addition(base) || !is_constant(exponent)) {
    return pow(base, exponent);
  }
  const mpq_class &e{get_constant_value(exponent)};
  if (e <= 0 || !is_integer(e)) {
    return pow(base, exponent);
  }
  const int n{static_cast<int>(e.get_num().get_si())};
  return ExpandPow(base, n);
}
}  // anonymous namespace

ExpressionCell::ExpressionCell(const ExpressionKind k)
    : kind_{k},
      variables_{},
      hash_{},
      is_polynomial_{},
      include_ite_{} {}
ExpressionCell::ExpressionCell(const ExpressionKind k, const bool is_poly)
    : kind_{k},
      variables_{},
      hash_{},
      is_polynomial_{is_poly},
      include_ite_{} {}
ExpressionCell::ExpressionCell(const ExpressionKind k, const bool is_poly, const bool include_ite)
    : kind_{k},
      variables_{},
      hash_{},
      is_polynomial_{is_poly},
      include_ite_{include_ite} {}
ExpressionCell::ExpressionCell(const ExpressionKind k, const bool is_poly, const bool include_ite, Variables variables)
    : kind_{k},
      variables_{std::move(variables)},
      hash_{},
      is_polynomial_{is_poly},
      include_ite_{include_ite} {}
ExpressionCell::ExpressionCell(const ExpressionKind k, const bool is_poly, const bool include_ite, Variables variables, const size_t hash)
    : kind_{k},
      variables_{std::move(variables)},
      hash_{hash_combine(static_cast<size_t>(kind_), hash)},
      is_polynomial_{is_poly},
      include_ite_{include_ite} {}

Expression ExpressionCell::GetExpression() { return Expression{this}; }

size_t ExpressionCell::get_hash() const {
  if (!hash_.has_value()) {
    ComputeHash(hash_);
    hash_.value() = hash_combine(static_cast<size_t>(kind_), hash_.value());
  }
  DLINEAR_ASSERT(hash_.has_value(), "hash_ must have a value.");
  return hash_.value();
}

bool ExpressionCell::is_polynomial() const {
  if (!is_polynomial_.has_value()) ComputeIsPolynomial(is_polynomial_);
  DLINEAR_ASSERT(is_polynomial_.has_value(), "is_polynomial_ must have a value.");
  return is_polynomial_.value();
}

bool ExpressionCell::include_ite() const {
  if (!include_ite_.has_value()) ComputeIncludeIte(include_ite_);
  DLINEAR_ASSERT(include_ite_.has_value(), "include_ite_ must have a value.");
  return include_ite_.value();
}

const Variables &ExpressionCell::GetVariables() const {
  if (!variables_.has_value()) ComputeVariables(variables_);
  DLINEAR_ASSERT(variables_.has_value(), "variables_ must have a value.");
  return variables_.value();
}

void ExpressionCell::UpdateHash() { hash_.reset(); }
void ExpressionCell::UpdateHash(const size_t hash) { hash_ = hash_combine(static_cast<size_t>(kind_), hash); }

void ExpressionCell::ComputeVariables(std::optional<Variables>&) const { DLINEAR_UNREACHABLE(); }
void ExpressionCell::ComputeHash(std::optional<size_t>&) const { DLINEAR_UNREACHABLE(); }
void ExpressionCell::ComputeIsPolynomial(std::optional<bool>&) const { DLINEAR_UNREACHABLE(); }
void ExpressionCell::ComputeIncludeIte(std::optional<bool>&) const { DLINEAR_UNREACHABLE(); }

UnaryExpressionCell::UnaryExpressionCell(const ExpressionKind k, const Expression &e, const bool is_poly)
    : ExpressionCell{k, is_poly}, e_{e} {}

void UnaryExpressionCell::ComputeHash(std::optional<size_t> &hash) const {
  assert(!hash.has_value());
  hash = e_.get_hash();
}
void UnaryExpressionCell::ComputeVariables(std::optional<Variables>& variables) const {
  assert(!variables.has_value());
  variables = e_.GetVariables();
}
void UnaryExpressionCell::ComputeIncludeIte(std::optional<bool>& include_ite) const {
  assert(!include_ite.has_value());
  include_ite = e_.include_ite();
}


bool UnaryExpressionCell::EqualTo(const ExpressionCell &e) const {
  // Expression::EqualTo guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  const auto &unary_e = static_cast<const UnaryExpressionCell &>(e);
  return e_.EqualTo(unary_e.e_);
}

bool UnaryExpressionCell::Less(const ExpressionCell &e) const {
  // Expression::Less guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  const auto &unary_e = static_cast<const UnaryExpressionCell &>(e);
  return e_.Less(unary_e.e_);
}

mpq_class UnaryExpressionCell::Evaluate(const Environment &env) const {
  const mpq_class &v{e_.Evaluate(env)};
  return DoEvaluate(v);
}

BinaryExpressionCell::BinaryExpressionCell(const ExpressionKind k, const Expression &e1, const Expression &e2, const bool is_poly)
    : ExpressionCell{k, is_poly},
      e1_{e1},
      e2_{e2} {}

void BinaryExpressionCell::ComputeHash(std::optional<size_t> &hash) const {
  assert(!hash.has_value());
  hash = hash_combine(e1_.get_hash(), e2_);
}
void BinaryExpressionCell::ComputeVariables(std::optional<Variables>& variables) const {
  assert(!variables.has_value());
  variables = e1_.GetVariables() + e2_.GetVariables();
}
void BinaryExpressionCell::ComputeIncludeIte(std::optional<bool>& include_ite) const {
  assert(!include_ite.has_value());
  include_ite = e1_.include_ite() || e2_.include_ite();
}

bool BinaryExpressionCell::EqualTo(const ExpressionCell &e) const {
  // Expression::EqualTo guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  const auto &binary_e = static_cast<const BinaryExpressionCell &>(e);
  return e1_.EqualTo(binary_e.e1_) && e2_.EqualTo(binary_e.e2_);
}

bool BinaryExpressionCell::Less(const ExpressionCell &e) const {
  // Expression::Less guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  const auto &binary_e = static_cast<const BinaryExpressionCell &>(e);
  if (e1_.Less(binary_e.e1_)) {
    return true;
  }
  if (binary_e.e1_.Less(e1_)) {
    return false;
  }
  // e1_ equals to binary_e.e1_, compare e2_ and binary_e.e2_
  return e2_.Less(binary_e.e2_);
}

mpq_class BinaryExpressionCell::Evaluate(const Environment &env) const {
  const mpq_class &v1{e1_.Evaluate(env)};
  const mpq_class &v2{e2_.Evaluate(env)};
  return DoEvaluate(v1, v2);
}

ExpressionVar::ExpressionVar(const Variable &v)
    : ExpressionCell{ExpressionKind::Var, true, false, {v}}, var_{v} {
  // Dummy symbolic variable (ID = 0) should not be used in constructing
  // symbolic expressions.
  if (var_.is_dummy()) {
    throw runtime_error("Dummy variable is used to construct an expression.");
  }
  // Boolean symbolic variable should not be used in constructing symbolic
  // expressions.
  if (var_.get_type() == Variable::Type::BOOLEAN) {
    ostringstream oss;
    oss << "Variable " << var_
        << " is of type BOOLEAN and it should not be used to construct a "
           "symbolic expression.";
    throw runtime_error(oss.str());
  }
}

void ExpressionVar::ComputeHash(std::optional<size_t>& hash) const {
  assert(!hash.has_value());
  hash = std::hash<Variable>{}(var_);
}

bool ExpressionVar::EqualTo(const ExpressionCell &e) const {
  // Expression::EqualTo guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  return var_.equal_to(static_cast<const ExpressionVar &>(e).var_);
}

bool ExpressionVar::Less(const ExpressionCell &e) const {
  // Expression::Less guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  // Note the below is using the overloaded operator< between ExpressionVar
  // which is based on variable IDs.
  return var_.less(static_cast<const ExpressionVar &>(e).var_);
}

mpq_class ExpressionVar::Evaluate(const Environment &env) const { return env.at(var_); }

Expression ExpressionVar::Expand() { return GetExpression(); }

Expression ExpressionVar::Substitute(const ExpressionSubstitution &expr_subst, const FormulaSubstitution &) {
  const ExpressionSubstitution::const_iterator it{expr_subst.find(var_)};
  if (it != expr_subst.end()) {
    return it->second;
  }
  return GetExpression();
}

Expression ExpressionVar::Differentiate(const Variable &x) const {
  if (x.equal_to(var_)) {
    return Expression::One();
  }
  return Expression::Zero();
}

ostream &ExpressionVar::Display(ostream &os) const { return os << var_; }
std::string ExpressionVar::to_smt2_string() const { return var_.to_string(); }

ExpressionConstant::ExpressionConstant(const mpq_class &v)
    : ExpressionCell{ExpressionKind::Constant, true, false, Variables{}}, v_{v} {}

void ExpressionConstant::ComputeHash(std::optional<size_t>& hash) const {
  assert(!hash.has_value());
  hash = std::hash<mpq_class>{}(v_);
}

bool ExpressionConstant::EqualTo(const ExpressionCell &e) const {
  // Expression::EqualTo guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  return v_ == static_cast<const ExpressionConstant &>(e).v_;
}

bool ExpressionConstant::Less(const ExpressionCell &e) const {
  // Expression::Less guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  return v_ < static_cast<const ExpressionConstant &>(e).v_;
}

void ExpressionConstant::UpdateHash() {
  ExpressionCell::UpdateHash(hash<mpq_class>{}(v_));
}

mpq_class ExpressionConstant::Evaluate(const Environment &) const { return v_; }

Expression ExpressionConstant::Expand() { return GetExpression(); }

Expression ExpressionConstant::Substitute(const ExpressionSubstitution &, const FormulaSubstitution &) {
  return GetExpression();
}

Expression ExpressionConstant::Differentiate(const Variable &) const { return Expression::Zero(); }

ostream &ExpressionConstant::Display(ostream &os) const {
  ostringstream oss;
  oss << v_;
  return os << oss.str();
}
std::string ExpressionConstant::to_smt2_string() const {
  return mpq_to_string(v_);
}

ExpressionNaN::ExpressionNaN() : ExpressionCell{ExpressionKind::NaN, false, false, Variables{}, 41} {
  // ExpressionCell constructor calls hash_combine(ExpressionKind::NaN, 41) to
  // compute the hash of ExpressionNaN. Here 41 does not have any special
  // meaning.
}

bool ExpressionNaN::EqualTo([[maybe_unused]] const ExpressionCell &e) const {
  // Expression::EqualTo guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  return true;
}

bool ExpressionNaN::Less([[maybe_unused]] const ExpressionCell &e) const {
  // Expression::Less guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  return false;
}

mpq_class ExpressionNaN::Evaluate(const Environment &) const {
  throw runtime_error("NaN is detected during Symbolic computation.");
}

Expression ExpressionNaN::Expand() { throw runtime_error("NaN is detected during expansion."); }

Expression ExpressionNaN::Substitute(const ExpressionSubstitution &, const FormulaSubstitution &) {
  throw runtime_error("NaN is detected during substitution.");
}

Expression ExpressionNaN::Differentiate(const Variable &) const {
  throw runtime_error("NaN is detected during differentiation.");
}

ostream &ExpressionNaN::Display(ostream &os) const { return os << "NaN"; }
std::string ExpressionNaN::to_smt2_string() const { return "NaN"; }

ExpressionInfty::ExpressionInfty(int sign)
    : ExpressionCell{ExpressionKind::Infty, false, false, Variables{}, 42}, sign_(sign) {
  // ExpressionCell constructor calls hash_combine(ExpressionKind::Infty, 42) to
  // compute the hash of ExpressionInfty. Here 42 does not have any special
  // meaning.
  if (sign_ != 1 && sign_ != -1) {
    throw runtime_error("Invalid sign when constructing ExpressionInfty.");
  }
}

bool ExpressionInfty::EqualTo(const ExpressionCell &e) const {
  // Expression::EqualTo guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  return sign_ == static_cast<const ExpressionInfty &>(e).sign_;
}

bool ExpressionInfty::Less(const ExpressionCell &e) const {
  // Expression::Less guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  return sign_ == -1 && static_cast<const ExpressionInfty &>(e).sign_ == 1;
}

mpq_class ExpressionInfty::Evaluate(const Environment &) const {
  throw runtime_error("An infinity is detected during Symbolic computation.");
}

Expression ExpressionInfty::Expand() { throw runtime_error("An infinity is detected during expansion."); }

Expression ExpressionInfty::Substitute(const ExpressionSubstitution &, const FormulaSubstitution &) {
  throw runtime_error("An infinity is detected during substitution.");
}

Expression ExpressionInfty::Differentiate(const Variable &) const {
  throw runtime_error("An infinity is detected during differentiation.");
}

ostream &ExpressionInfty::Display(ostream &os) const { return os << (sign_ == -1 ? "-" : "") << "infinity"; }
std::string ExpressionInfty::to_smt2_string() const { return (sign_ == -1 ? "-infinity" : "infinity"); }

ExpressionAdd::ExpressionAdd(const mpq_class &constant, map<Expression, mpq_class> expr_to_coeff_map)
    : ExpressionCell{ExpressionKind::Add},
      constant_(constant),
      expr_to_coeff_map_{std::move(expr_to_coeff_map)} {
  assert(!expr_to_coeff_map_.empty());
}

void ExpressionAdd::UpdateHash() {
  ExpressionCell::UpdateHash(hash_combine(hash<mpq_class>{}(constant_), expr_to_coeff_map_));
}

void ExpressionAdd::ComputeVariables(std::optional<Variables>& variables) const {
  assert(!variables.has_value());
  variables = Variables{};
  for (const auto &p : expr_to_coeff_map_) {
    variables.value().insert(p.first.GetVariables());
  }
}
void ExpressionAdd::ComputeHash(std::optional<size_t>& hash) const {
  assert(!hash.has_value());
  hash = hash_combine(std::hash<mpq_class>{}(constant_), expr_to_coeff_map_);
}
void ExpressionAdd::ComputeIsPolynomial(std::optional<bool>& is_polynomial) const {
    assert(!is_polynomial.has_value());
    is_polynomial = determine_polynomial(expr_to_coeff_map_);
}
void ExpressionAdd::ComputeIncludeIte(std::optional<bool>& include_ite) const {
  assert(!include_ite.has_value());
  include_ite = determine_include_ite(expr_to_coeff_map_);
}

bool ExpressionAdd::EqualTo(const ExpressionCell &e) const {
  // Expression::EqualTo guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  const ExpressionAdd &add_e{static_cast<const ExpressionAdd &>(e)};
  // Compare constant.
  if (constant_ != add_e.constant_) {
    return false;
  }
  return equal(expr_to_coeff_map_.cbegin(), expr_to_coeff_map_.cend(), add_e.expr_to_coeff_map_.cbegin(),
               add_e.expr_to_coeff_map_.cend(),
               [](const pair<const Expression, mpq_class> &p1, const pair<const Expression, mpq_class> &p2) {
                 return p1.first.EqualTo(p2.first) && p1.second == p2.second;
               });
}

bool ExpressionAdd::Less(const ExpressionCell &e) const {
  // Expression::Less guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  const ExpressionAdd &add_e{static_cast<const ExpressionAdd &>(e)};
  // Compare the constants.
  if (constant_ < add_e.constant_) {
    return true;
  }
  if (add_e.constant_ < constant_) {
    return false;
  }
  // Compare the two maps.
  return lexicographical_compare(
      expr_to_coeff_map_.cbegin(), expr_to_coeff_map_.cend(), add_e.expr_to_coeff_map_.cbegin(),
      add_e.expr_to_coeff_map_.cend(),
      [](const pair<const Expression, mpq_class> &p1, const pair<const Expression, mpq_class> &p2) {
        const Expression &term1{p1.first};
        const Expression &term2{p2.first};
        if (term1.Less(term2)) {
          return true;
        }
        if (term2.Less(term1)) {
          return false;
        }
        const mpq_class &coeff1{p1.second};
        const mpq_class &coeff2{p2.second};
        return coeff1 < coeff2;
      });
}

mpq_class ExpressionAdd::Evaluate(const Environment &env) const {
  return accumulate(expr_to_coeff_map_.begin(), expr_to_coeff_map_.end(), constant_,
                    [&env](const mpq_class &init, const pair<const Expression, mpq_class> &p) {
                      // Without the cast, it would return an expression template
                      return static_cast<mpq_class>(init + p.first.Evaluate(env) * p.second);
                    });
}

Expression ExpressionAdd::Expand() {
  //   (c0 + c1 * e_1 + ... + c_n * e_n).Expand()
  // =  c0 + c1 * e_1.Expand() + ... + c_n * e_n.Expand()
  Expression ret{constant_};
  for (const auto &p : expr_to_coeff_map_) {
    const Expression &e_i{p.first};
    const mpq_class &c_i{p.second};
    ret += ExpandMultiplication(e_i.Expand(), c_i);
  }
  return ret;
}

Expression ExpressionAdd::Substitute(const ExpressionSubstitution &expr_subst,
                                     const FormulaSubstitution &formula_subst) {
  Expression ret{constant_};
  for (const auto &p : expr_to_coeff_map_) {
    const Expression &e_i{p.first};
    const mpq_class &c_i{p.second};
    ret += e_i.Substitute(expr_subst, formula_subst) * c_i;
  }
  return ret;
}

Expression ExpressionAdd::Differentiate(const Variable &x) const {
  //   ∂/∂x (c_0 + c_1 * f_1 + ... + c_n * f_n)
  // = (∂/∂x c_0) + (∂/∂x c_1 * f_1) + ... + (∂/∂x c_n * f_n)
  // =  0.0       + c_1 * (∂/∂x f_1) + ... + c_n * (∂/∂x f_n)
  Expression ret{Expression::Zero()};
  for (const auto &p : expr_to_coeff_map_) {
    const Expression &e_i{p.first};
    const mpq_class &c_i{p.second};
    ret += c_i * e_i.Differentiate(x);
  }
  return ret;
}

ostream &ExpressionAdd::Display(ostream &os) const {
  assert(!expr_to_coeff_map_.empty());
  bool print_plus{false};
  os << "(";
  if (constant_ != 0.0) {
    os << constant_;
    print_plus = true;
  }
  for (auto &p : expr_to_coeff_map_) {
    DisplayTerm(os, print_plus, p.second, p.first);
    print_plus = true;
  }
  os << ")";
  return os;
}
std::string ExpressionAdd::to_smt2_string() const {
  std::string ret = "(+ ";
  if (constant_ != 0.0) {
    ret += mpq_to_string(constant_);
  }
  for (auto &[var, coeff] : expr_to_coeff_map_) {
    if (coeff == 1)
      ret += " " + var.to_smt2_string() + " ";
    else
      ret += " (* " + mpq_to_string(coeff) + " " + var.to_smt2_string() + ") ";
  }
  ret += ")";
  return ret;
}

ostream &ExpressionAdd::DisplayTerm(ostream &os, const bool print_plus, const mpq_class &coeff,
                                    const Expression &term) const {
  assert(coeff != 0.0);
  if (coeff > 0.0) {
    if (print_plus) {
      os << " + ";
    }
    // Do not print "1 * t"
    if (coeff != 1.0) {
      os << coeff << " * ";
    }
  } else {
    // Instead of printing "+ (- E)", just print "- E".
    os << " - ";
    if (coeff != -1.0) {
      os << (-coeff) << " * ";
    }
  }
  os << term;
  return os;
}
ExpressionAddFactory::ExpressionAddFactory(const mpq_class &constant, const map<Expression, mpq_class>& expr_to_coeff_map)
    : get_expression_is_called_{false}, constant_{constant}, expr_to_coeff_map_{expr_to_coeff_map} {}
ExpressionAddFactory::ExpressionAddFactory(mpq_class &&constant, map<Expression, mpq_class>&& expr_to_coeff_map)
    : get_expression_is_called_{false}, constant_{std::move(constant)}, expr_to_coeff_map_{std::move(expr_to_coeff_map)} {}

ExpressionAddFactory::ExpressionAddFactory(const ExpressionAdd *const ptr)
    : ExpressionAddFactory{ptr->get_constant(), ptr->get_expr_to_coeff_map()} {}

ExpressionAddFactory &ExpressionAddFactory::AddExpression(const Expression &e) {
  if (is_constant(e)) {
    const mpq_class &v{get_constant_value(e)};
    return AddConstant(v);
  }
  if (is_addition(e)) {
    // Flattening
    return Add(to_addition(e));
  }
  if (is_multiplication(e)) {
    const mpq_class &constant{get_constant_in_multiplication(e)};
    if (constant != 1.0) {
      // Instead of adding (1.0 * (constant * b1^t1 ... bn^tn)),
      // add (constant, 1.0 * b1^t1 ... bn^tn).
      return AddTerm(constant,
                     ExpressionMulFactory(1.0, get_base_to_exponent_map_in_multiplication(e)).GetExpression());
    }
  }
  return AddTerm(1.0, e);
}

ExpressionAddFactory &ExpressionAddFactory::Add(const ExpressionAdd *const ptr) {
  AddConstant(ptr->get_constant());
  return AddMap(ptr->get_expr_to_coeff_map());
}

ExpressionAddFactory &ExpressionAddFactory::operator=(const ExpressionAdd *const ptr) {
  constant_ = ptr->get_constant();
  expr_to_coeff_map_ = ptr->get_expr_to_coeff_map();
  return *this;
}

ExpressionAddFactory &ExpressionAddFactory::Negate() {
  constant_ = -constant_;
  for (auto &p : expr_to_coeff_map_) {
    p.second = -p.second;
  }
  return *this;
}

Expression ExpressionAddFactory::GetExpression() {
  if (get_expression_is_called_) {
    throw runtime_error(
        "ExpressionAddFactory::GetExpression() is already called, and it "
        "should not be invoked again.");
  }
  get_expression_is_called_ = true;
  if (expr_to_coeff_map_.empty()) {
    return Expression{constant_};
  }
  if (constant_ == 0.0 && expr_to_coeff_map_.size() == 1U) {
    // 0.0 + c1 * t1 -> c1 * t1
    const auto it(expr_to_coeff_map_.cbegin());
    return it->first * it->second;
  }
  return Expression{new ExpressionAdd(constant_, std::move(expr_to_coeff_map_))};
}

ExpressionAddFactory &ExpressionAddFactory::AddConstant(const mpq_class &constant) {
  constant_ += constant;
  return *this;
}

ExpressionAddFactory &ExpressionAddFactory::AddTerm(const mpq_class &coeff, const Expression &term) {
  assert(!is_constant(term));

  const auto it(expr_to_coeff_map_.find(term));
  if (it != expr_to_coeff_map_.end()) {
    // Case1: term is already in the map
    mpq_class &this_coeff{it->second};
    this_coeff += coeff;
    if (this_coeff == 0.0) {
      // If the coefficient becomes zero, remove the entry.
      // TODO(soonho-tri): The following operation is not sound since it cancels
      // `term` which might contain 0/0 problems.
      expr_to_coeff_map_.erase(it);
    }
  } else {
    // Case2: term is not found in expr_to_coeff_map_.
    // Add the entry (term, coeff).
    expr_to_coeff_map_.emplace(term, coeff);
  }
  return *this;
}

ExpressionAddFactory &ExpressionAddFactory::AddMap(const map<Expression, mpq_class> &expr_to_coeff_map) {
  for (const auto &p : expr_to_coeff_map) {
    AddTerm(p.second, p.first);
  }
  return *this;
}

ExpressionMul::ExpressionMul(const mpq_class &constant, map<Expression, Expression> base_to_exponent_map)
    : ExpressionCell{ExpressionKind::Mul},
      constant_(constant),
      base_to_exponent_map_{std::move(base_to_exponent_map)} {
  assert(!base_to_exponent_map_.empty());
}

void ExpressionMul::ComputeVariables(std::optional<Variables>& variables) const {
  assert(!variables.has_value());
  variables = Variables{};
  for (const auto &[base, exponent] : base_to_exponent_map_) {
    variables.value().insert(base.GetVariables());
    variables.value().insert(exponent.GetVariables());
  }
}
void ExpressionMul::ComputeHash(std::optional<size_t>& hash) const {
  assert(!hash.has_value());
  hash = hash_combine(std::hash<mpq_class>{}(constant_), base_to_exponent_map_);
}
void ExpressionMul::ComputeIsPolynomial(std::optional<bool>& is_polynomial) const {
  assert(!is_polynomial.has_value());
  is_polynomial = determine_polynomial(base_to_exponent_map_);
}
void ExpressionMul::ComputeIncludeIte(std::optional<bool>& include_ite) const {
  assert(!include_ite.has_value());
  include_ite = determine_include_ite(base_to_exponent_map_);
}

bool ExpressionMul::EqualTo(const ExpressionCell &e) const {
  // Expression::EqualTo guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  const ExpressionMul &mul_e{static_cast<const ExpressionMul &>(e)};
  // Compare constant.
  if (constant_ != mul_e.constant_) {
    return false;
  }
  // Check each (term, coeff) pairs in two maps.
  return equal(base_to_exponent_map_.cbegin(), base_to_exponent_map_.cend(), mul_e.base_to_exponent_map_.cbegin(),
               mul_e.base_to_exponent_map_.cend(),
               [](const pair<const Expression, Expression> &p1, const pair<const Expression, Expression> &p2) {
                 return p1.first.EqualTo(p2.first) && p1.second.EqualTo(p2.second);
               });
}

bool ExpressionMul::Less(const ExpressionCell &e) const {
  // Expression::Less guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  const ExpressionMul &mul_e{static_cast<const ExpressionMul &>(e)};
  // Compare the constants.
  if (constant_ < mul_e.constant_) {
    return true;
  }
  if (mul_e.constant_ < constant_) {
    return false;
  }
  // Compare the two maps.
  return lexicographical_compare(
      base_to_exponent_map_.cbegin(), base_to_exponent_map_.cend(), mul_e.base_to_exponent_map_.cbegin(),
      mul_e.base_to_exponent_map_.cend(),
      [](const pair<const Expression, Expression> &p1, const pair<const Expression, Expression> &p2) {
        const Expression &base1{p1.first};
        const Expression &base2{p2.first};
        if (base1.Less(base2)) {
          return true;
        }
        if (base2.Less(base1)) {
          return false;
        }
        const Expression &exp1{p1.second};
        const Expression &exp2{p2.second};
        return exp1.Less(exp2);
      });
}

mpq_class ExpressionMul::Evaluate(const Environment &env) const {
  return accumulate(base_to_exponent_map_.begin(), base_to_exponent_map_.end(), constant_,
                    [&env](const mpq_class &init, const pair<const Expression, Expression> &p) {
                      mpq_class exponent{p.second.Evaluate(env)};
                      if (exponent == 1) {
                        // Without the cast, it would return an expression template
                        return static_cast<mpq_class>(init * p.first.Evaluate(env));
                      } else if (exponent == 0) {
                        return init;
                      } else {
                        throw runtime_error("Not implemented");  // Because of mpq_class
                      }
                    });
}

Expression ExpressionMul::Expand() {
  //   (c * ∏ᵢ pow(bᵢ, eᵢ)).Expand()
  // = c * ExpandMultiplication(∏ ExpandPow(bᵢ.Expand(), eᵢ.Expand()))
  Expression ret{constant_};
  for (const auto &p : base_to_exponent_map_) {
    const Expression &b_i{p.first};
    const Expression &e_i{p.second};
    ret = ExpandMultiplication(ret, ExpandPow(b_i.Expand(), e_i.Expand()));
  }
  return ret;
}

Expression ExpressionMul::Substitute(const ExpressionSubstitution &expr_subst,
                                     const FormulaSubstitution &formula_subst) {
  Expression ret{constant_};
  for (const auto &p : base_to_exponent_map_) {
    const Expression &b_i{p.first};
    const Expression &e_i{p.second};
    ret *= pow(b_i.Substitute(expr_subst, formula_subst), e_i.Substitute(expr_subst, formula_subst));
  }
  return ret;
}

// Computes ∂/∂x pow(f, g).
Expression DifferentiatePow(const Expression &f, const Expression &g, const Variable &x) {
  if (is_constant(g)) {
    const Expression &n{g};  // alias n = g
    // Special case where exponent is a constant:
    //     ∂/∂x pow(f, n) = n * pow(f, n - 1) * ∂/∂x f
    return n * pow(f, n - 1) * f.Differentiate(x);
  }
  if (is_constant(f)) {
    const Expression &n{f};  // alias n = f
    // Special case where base is a constant:
    //     ∂/∂x pow(n, g) = log(n) * pow(n, g) * ∂/∂x g
    return log(n) * pow(n, g) * g.Differentiate(x);
  }
  // General case:
  //    ∂/∂x pow(f, g)
  // = ∂/∂f pow(f, g) * ∂/∂x f + ∂/∂g pow(f, g) * ∂/∂x g
  // = g * pow(f, g - 1) * ∂/∂x f + log(f) * pow(f, g) * ∂/∂x g
  // = pow(f, g - 1) * (g * ∂/∂x f + log(f) * f * ∂/∂x g)
  return pow(f, g - 1) * (g * f.Differentiate(x) + log(f) * f * g.Differentiate(x));
}

Expression ExpressionMul::Differentiate(const Variable &x) const {
  // ∂/∂x (c   * f_1^g_1  * f_2^g_2        * ... * f_n^g_n
  //= c * [expr * (∂/∂x f_1^g_1) / f_1^g_1 +
  //       expr * (∂/∂x f_2^g_2) / f_2^g_2 +
  //                      ...              +
  //       expr * (∂/∂x f_n^g_n) / f_n^g_n]
  //
  // where expr = (f_1^g_1 * f_2^g_2 * ... * f_n^g_n).
  const map<Expression, Expression> &m{base_to_exponent_map_};
  Expression ret{Expression::Zero()};
  const Expression expr{ExpressionMulFactory{1.0, base_to_exponent_map_}.GetExpression()};
  for (const auto &term : m) {
    const Expression &base{term.first};
    const Expression &exponent{term.second};
    ret += expr * DifferentiatePow(base, exponent, x) * pow(base, -exponent);
  }
  return constant_ * ret;
}

ostream &ExpressionMul::Display(ostream &os) const {
  assert(!base_to_exponent_map_.empty());
  bool print_mul{false};
  os << "(";
  if (constant_ != 1.0) {
    os << constant_;
    print_mul = true;
  }
  for (auto &p : base_to_exponent_map_) {
    DisplayTerm(os, print_mul, p.first, p.second);
    print_mul = true;
  }
  os << ")";
  return os;
}
std::string ExpressionMul::to_smt2_string() const {
  std::string ret = "(* ";
  if (constant_ != 1.0) {
    ret += mpq_to_string(constant_);
  }
  for (auto &[var, exp] : base_to_exponent_map_) {
    if (exp == 1)
      ret += " " + var.to_smt2_string();
    else
      ret += " (pow " + var.to_smt2_string() + " " + exp.to_smt2_string() + ")";
  }
  ret += ")";
  return ret;
}

ostream &ExpressionMul::DisplayTerm(ostream &os, const bool print_mul, const Expression &base,
                                    const Expression &exponent) const {
  // Print " * pow(base, exponent)" if print_mul is true
  // Print "pow(base, exponent)" if print_mul is false
  // Print "base" instead of "pow(base, exponent)" if exponent == 1.0
  if (print_mul) {
    os << " * ";
  }
  if (is_one(exponent)) {
    os << base;
  } else {
    os << "pow(" << base << ", " << exponent << ")";
  }
  return os;
}

ExpressionMulFactory::ExpressionMulFactory(const mpq_class &constant, const map<Expression, Expression>& base_to_exponent_map)
    : get_expression_is_called_{false}, constant_{constant}, base_to_exponent_map_{base_to_exponent_map} {}

ExpressionMulFactory::ExpressionMulFactory(mpq_class &&constant, map<Expression, Expression>&& base_to_exponent_map)
    : get_expression_is_called_{false}, constant_{std::move(constant)}, base_to_exponent_map_{std::move(base_to_exponent_map)} {}

ExpressionMulFactory::ExpressionMulFactory(const ExpressionMul *const ptr)
    : ExpressionMulFactory{ptr->get_constant(), ptr->get_base_to_exponent_map()} {}

ExpressionMulFactory &ExpressionMulFactory::AddExpression(const Expression &e) {
  if (is_constant(e)) {
    return AddConstant(get_constant_value(e));
  }
  if (is_multiplication(e)) {
    // Flattening
    return Add(to_multiplication(e));
  }
  if (is_pow(e)) {
    return AddTerm(get_first_argument(e), get_second_argument(e));
  }
  // Add e^1
  return AddTerm(e, Expression{1});
}

ExpressionMulFactory &ExpressionMulFactory::Add(const ExpressionMul *const ptr) {
  AddConstant(ptr->get_constant());
  return AddMap(ptr->get_base_to_exponent_map());
}

ExpressionMulFactory &ExpressionMulFactory::operator=(const ExpressionMul *const ptr) {
  constant_ = ptr->get_constant();
  base_to_exponent_map_ = ptr->get_base_to_exponent_map();
  return *this;
}

ExpressionMulFactory &ExpressionMulFactory::Negate() {
  constant_ = -constant_;
  return *this;
}

Expression ExpressionMulFactory::GetExpression() {
  if (get_expression_is_called_) {
    throw runtime_error(
        "ExpressionMulFactory::GetExpression() is already called, and it "
        "should not be invoked again.");
  }
  get_expression_is_called_ = true;
  if (base_to_exponent_map_.empty()) {
    return Expression{constant_};
  }
  if (constant_ == 1.0 && base_to_exponent_map_.size() == 1U) {
    // 1.0 * c1^t1 -> c1^t1
    const auto it(base_to_exponent_map_.cbegin());
    return pow(it->first, it->second);
  }
  return Expression{new ExpressionMul(constant_, std::move(base_to_exponent_map_))};
}

ExpressionMulFactory &ExpressionMulFactory::AddConstant(const mpq_class &constant) {
  constant_ *= constant;
  return *this;
}

ExpressionMulFactory &ExpressionMulFactory::AddTerm(const Expression &base, const Expression &exponent) {
  // The following assertion holds because of
  // ExpressionMulFactory::AddExpression.
  assert(!(is_constant(base) && is_constant(exponent)));
  if (is_pow(base) && is_constant(exponent)) {
    const Expression &e2{get_second_argument(base)};
    if (is_constant(e2)) {
      const mpq_class &e2_value{get_constant_value(e2)};
      if (is_integer(e2_value)) {
        // If base = pow(e1, e2) and both of e2 and exponent are
        // integers, then add (e1, e2 * exponent).
        //
        // Example: (x^2)^3 => x^(2 * 3)
        const Expression &e1{get_first_argument(base)};
        return AddTerm(e1, e2 * exponent);
      }
    }
  }

  const auto it(base_to_exponent_map_.find(base));
  if (it != base_to_exponent_map_.end()) {
    // base is already in map.
    // (= b1^e1 * ... * (base^this_exponent) * ... * en^bn).
    // Update it to be (... * (base^(this_exponent + exponent)) * ...)
    // Example: x^3 * x^2 => x^5
    Expression &this_exponent = it->second;
    this_exponent += exponent;
    if (is_zero(this_exponent)) {
      // If it ends up with base^0 (= 1.0) then remove this entry from the map.
      // TODO(soonho-tri): The following operation is not sound since it can
      // cancels `base` which might include 0/0 problems.
      base_to_exponent_map_.erase(it);
    }
  } else {
    // Product is not found in base_to_exponent_map_. Add the entry (base,
    // exponent).
    base_to_exponent_map_.emplace(base, exponent);
  }
  return *this;
}

ExpressionMulFactory &ExpressionMulFactory::AddMap(const map<Expression, Expression> &base_to_exponent_map) {
  for (const auto &p : base_to_exponent_map) {
    AddTerm(p.first, p.second);
  }
  return *this;
}

ExpressionDiv::ExpressionDiv(const Expression &e1, const Expression &e2)
    : BinaryExpressionCell{ExpressionKind::Div, e1, e2, e1.is_polynomial() && is_constant(e2)} {}

namespace {
// Helper class to implement ExpressionDiv::Expand. Given a symbolic expression
// `e` and a constant `n`, it pushes the division in `e / n` inside for the
// following cases:
//
// Case Addition      : e =  (c₀ + ∑ᵢ (cᵢ * eᵢ)) / n
//                        => c₀/n + ∑ᵢ (cᵢ / n * eᵢ)
//
// Case Multiplication: e =  (c₀ * ∏ᵢ (bᵢ * eᵢ)) / n
//                        => c₀ / n * ∏ᵢ (bᵢ * eᵢ)
//
// Case Division      : e =  (e₁ / m) / n
//                        => Recursively simplify e₁ / (n * m)
//
//                      e =  (e₁ / e₂) / n
//                        =  (e₁ / n) / e₂
//                        => Recursively simplify (e₁ / n) and divide it by e₂
//
// For other cases, it does not perform any simplifications.
//
// Note that we use VisitExpression instead of VisitPolynomial because we want
// to handle cases such as `(6xy / z) / 3` where (6xy / z) is not a polynomial
// but it's desirable to simplify the expression into `2xy / z`.
class DivExpandVisitor {
 public:
  Expression Simplify(const Expression &e, const mpq_class &n) const { return VisitExpression<Expression>(this, e, n); }

 private:
  Expression VisitAddition(const Expression &e, const mpq_class &n) const {
    // e =  (c₀ + ∑ᵢ (cᵢ * eᵢ)) / n
    //   => c₀/n + ∑ᵢ (cᵢ / n * eᵢ)
    const mpq_class &constant{get_constant_in_addition(e)};
    ExpressionAddFactory factory(constant / n, {});
    for (const pair<const Expression, mpq_class> &p : get_expr_to_coeff_map_in_addition(e)) {
      factory.AddExpression(Expression(p.second / n) * p.first);
    }
    return factory.GetExpression();
  }
  Expression VisitMultiplication(const Expression &e, const mpq_class &n) const {
    // e =  (c₀ * ∏ᵢ (bᵢ * eᵢ)) / n
    //   => c₀ / n * ∏ᵢ (bᵢ * eᵢ)
    return ExpressionMulFactory{get_constant_in_multiplication(e) / n, get_base_to_exponent_map_in_multiplication(e)}
        .GetExpression();
  }
  Expression VisitDivision(const Expression &e, const mpq_class &n) const {
    const Expression &e1{get_first_argument(e)};
    const Expression &e2{get_second_argument(e)};
    if (is_constant(e2)) {
      // e =  (e₁ / m) / n
      //   => Simplify `e₁ / (n * m)`
      const mpq_class &m{get_constant_value(e2)};
      return Simplify(e1, m * n);
    } else {
      // e =  (e₁ / e₂) / n
      //   => (e₁ / n) / e₂
      return Simplify(e1, n) / e2;
    }
  }
  Expression VisitVariable(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitConstant(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitLog(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitPow(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitAbs(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitExp(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitSqrt(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitSin(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitCos(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitTan(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitAsin(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitAcos(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitAtan(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitAtan2(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitSinh(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitCosh(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitTanh(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitMin(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitMax(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitIfThenElse(const Expression &e, const mpq_class &n) const { return e / n; }
  Expression VisitUninterpretedFunction(const Expression &e, const mpq_class &n) const { return e / n; }

  // Makes VisitExpression a friend of this class so that VisitExpression can
  // use its private methods.
  friend Expression dlinear::drake::symbolic::VisitExpression<Expression>(const DivExpandVisitor *, const Expression &,
                                                                          const mpq_class &);
};
}  // namespace

Expression ExpressionDiv::Expand() {
  const Expression &e1{get_first_argument()};
  const Expression &e2{get_second_argument()};
  const Expression e1_expand{e1.Expand()};
  if (is_constant(e2)) {
    // Simplifies the 'division by a constant' case, using DivExpandVisitor
    // defined above.
    return DivExpandVisitor{}.Simplify(e1_expand, get_constant_value(e2));
  }
  const Expression e2_expand{e2.Expand()};
  if (!e1.EqualTo(e1_expand) || !e2.EqualTo(e2_expand)) {
    return e1_expand / e2_expand;
  } else {
    return GetExpression();
  }
}

Expression ExpressionDiv::Substitute(const ExpressionSubstitution &expr_subst,
                                     const FormulaSubstitution &formula_subst) {
  const Expression &e1{get_first_argument()};
  const Expression &e2{get_second_argument()};
  const Expression e1_subst{e1.Substitute(expr_subst, formula_subst)};
  const Expression e2_subst{e2.Substitute(expr_subst, formula_subst)};
  if (!e1.EqualTo(e1_subst) || !e2.EqualTo(e2_subst)) {
    // If anything changed, create and return a new one.
    return e1_subst / e2_subst;
  } else {
    // Otherwise, return self.
    return GetExpression();
  }
}

Expression ExpressionDiv::Differentiate(const Variable &x) const {
  // ∂/∂x (f / g) = (∂/∂x f * g - f * ∂/∂x g) / g^2
  const Expression &f{get_first_argument()};
  const Expression &g{get_second_argument()};
  return (f.Differentiate(x) * g - f * g.Differentiate(x)) / pow(g, 2.0);
}

ostream &ExpressionDiv::Display(ostream &os) const {
  return os << "(" << get_first_argument() << " / " << get_second_argument() << ")";
}
std::string ExpressionDiv::to_smt2_string() const {
  return "(/ " + get_first_argument().to_smt2_string() + " " + get_second_argument().to_smt2_string() + ")";
}

mpq_class ExpressionDiv::DoEvaluate(const mpq_class &v1, const mpq_class &v2) const {
  if (v2 == 0.0) {
    ostringstream oss;
    oss << "Division by zero: " << v1 << " / " << v2;
    this->Display(oss) << endl;
    throw runtime_error(oss.str());
  }
  return v1 / v2;
}

ExpressionLog::ExpressionLog(const Expression &e) : UnaryExpressionCell{ExpressionKind::Log, e, false} {}

void ExpressionLog::check_domain(const mpq_class &v) {
  if (!(v >= 0)) {
    ostringstream oss;
    oss << "log(" << v << ") : numerical argument out of domain. " << v << " is not in [0, +oo)" << endl;
    throw domain_error(oss.str());
  }
}

Expression ExpressionLog::Expand() {
  const Expression &arg{get_argument()};
  const Expression arg_expanded{arg.Expand()};
  if (!arg.EqualTo(arg_expanded)) {
    return log(arg_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionLog::Substitute(const ExpressionSubstitution &expr_subst,
                                     const FormulaSubstitution &formula_subst) {
  const Expression &arg{get_argument()};
  const Expression arg_subst{arg.Substitute(expr_subst, formula_subst)};
  if (!arg.EqualTo(arg_subst)) {
    return log(arg_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionLog::Differentiate(const Variable &x) const {
  // ∂/∂x log(f) = (∂/∂x f) / f
  const Expression &f{get_argument()};
  return f.Differentiate(x) / f;
}

ostream &ExpressionLog::Display(ostream &os) const { return os << "log(" << get_argument() << ")"; }
std::string ExpressionLog::to_smt2_string() const { return "(log " + get_argument().to_smt2_string() + ")"; }

mpq_class ExpressionLog::DoEvaluate(const mpq_class &) const {
  throw runtime_error("Not implemented");  // Because of mpq_class
#if 0
  check_domain(v);
  return std::log(v);
#endif
}

ExpressionAbs::ExpressionAbs(const Expression &e) : UnaryExpressionCell{ExpressionKind::Abs, e, false} {}

Expression ExpressionAbs::Expand() {
  const Expression &arg{get_argument()};
  const Expression arg_expanded{arg.Expand()};
  if (!arg.EqualTo(arg_expanded)) {
    return abs(arg_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionAbs::Substitute(const ExpressionSubstitution &expr_subst,
                                     const FormulaSubstitution &formula_subst) {
  const Expression &arg{get_argument()};
  const Expression arg_subst{arg.Substitute(expr_subst, formula_subst)};
  if (!arg.EqualTo(arg_subst)) {
    return abs(arg_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionAbs::Differentiate(const Variable &x) const {
  if (GetVariables().include(x)) {
    ostringstream oss;
    Display(oss) << "is not differentiable with respect to " << x << ".";
    throw runtime_error(oss.str());
  } else {
    return Expression::Zero();
  }
}

ostream &ExpressionAbs::Display(ostream &os) const { return os << "abs(" << get_argument() << ")"; }
std::string ExpressionAbs::to_smt2_string() const { return "(abs " + get_argument().to_smt2_string() + ")"; }

mpq_class ExpressionAbs::DoEvaluate(const mpq_class &v) const { return abs(v); }

ExpressionExp::ExpressionExp(const Expression &e) : UnaryExpressionCell{ExpressionKind::Exp, e, false} {}

Expression ExpressionExp::Expand() {
  const Expression &arg{get_argument()};
  const Expression arg_expanded{arg.Expand()};
  if (!arg.EqualTo(arg_expanded)) {
    return exp(arg_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionExp::Substitute(const ExpressionSubstitution &expr_subst,
                                     const FormulaSubstitution &formula_subst) {
  const Expression &arg{get_argument()};
  const Expression arg_subst{arg.Substitute(expr_subst, formula_subst)};
  if (!arg.EqualTo(arg_subst)) {
    return exp(arg_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionExp::Differentiate(const Variable &x) const {
  // ∂/∂x exp(f) = exp(f) * (∂/∂x f)
  const Expression &f{get_argument()};
  return exp(f) * f.Differentiate(x);
}

ostream &ExpressionExp::Display(ostream &os) const { return os << "exp(" << get_argument() << ")"; }
std::string ExpressionExp::to_smt2_string() const { return "(exp " + get_argument().to_smt2_string() + ")"; }

mpq_class ExpressionExp::DoEvaluate(const mpq_class &) const {
  throw runtime_error("Not implemented");  // Because of mpq_class
  // return std::exp(v);
}

ExpressionSqrt::ExpressionSqrt(const Expression &e) : UnaryExpressionCell{ExpressionKind::Sqrt, e, false} {}

void ExpressionSqrt::check_domain(const mpq_class &v) {
  if (!(v >= 0)) {
    ostringstream oss;
    oss << "sqrt(" << v << ") : numerical argument out of domain. " << v << " is not in [0, +oo)" << endl;
    throw domain_error(oss.str());
  }
}

Expression ExpressionSqrt::Expand() {
  const Expression &arg{get_argument()};
  const Expression arg_expanded{arg.Expand()};
  if (!arg.EqualTo(arg_expanded)) {
    return sqrt(arg_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionSqrt::Substitute(const ExpressionSubstitution &expr_subst,
                                      const FormulaSubstitution &formula_subst) {
  const Expression &arg{get_argument()};
  const Expression arg_subst{arg.Substitute(expr_subst, formula_subst)};
  if (!arg.EqualTo(arg_subst)) {
    return sqrt(arg_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionSqrt::Differentiate(const Variable &x) const {
  // ∂/∂x (sqrt(f)) = 1 / (2 * sqrt(f)) * (∂/∂x f)
  const Expression &f{get_argument()};
  return 1 / (2 * sqrt(f)) * f.Differentiate(x);
}

ostream &ExpressionSqrt::Display(ostream &os) const { return os << "sqrt(" << get_argument() << ")"; }
std::string ExpressionSqrt::to_smt2_string() const { return "(sqrt " + get_argument().to_smt2_string() + ")"; }

mpq_class ExpressionSqrt::DoEvaluate(const mpq_class &) const {
  throw runtime_error("Not implemented");  // Because of mpq_class
#if 0
  check_domain(v);
  return std::sqrt(v);
#endif
}

ExpressionPow::ExpressionPow(const Expression &e1, const Expression &e2)
    : BinaryExpressionCell{ExpressionKind::Pow, e1, e2, determine_polynomial(e1, e2)} {}

void ExpressionPow::check_domain(const mpq_class &v1, const mpq_class &v2) {
  if ((v1 < 0.0) && !is_integer(v2)) {
    ostringstream oss;
    oss << "pow(" << v1 << ", " << v2 << ") : numerical argument out of domain. " << v1 << " is finite negative and "
        << v2 << " is finite non-integer." << endl;
    throw domain_error(oss.str());
  }
}

Expression ExpressionPow::Expand() {
  const Expression &arg1{get_first_argument()};
  const Expression &arg2{get_second_argument()};
  const Expression arg1_expanded{arg1.Expand()};
  const Expression arg2_expanded{arg2.Expand()};
  return ExpandPow(arg1_expanded, arg2_expanded);
}

Expression ExpressionPow::Substitute(const ExpressionSubstitution &expr_subst,
                                     const FormulaSubstitution &formula_subst) {
  const Expression &arg1{get_first_argument()};
  const Expression &arg2{get_second_argument()};
  const Expression arg1_subst{arg1.Substitute(expr_subst, formula_subst)};
  const Expression arg2_subst{arg2.Substitute(expr_subst, formula_subst)};
  if (!arg1.EqualTo(arg1_subst) || !arg2.EqualTo(arg2_subst)) {
    return pow(arg1_subst, arg2_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionPow::Differentiate(const Variable &x) const {
  return DifferentiatePow(get_first_argument(), get_second_argument(), x);
}

ostream &ExpressionPow::Display(ostream &os) const {
  return os << "pow(" << get_first_argument() << ", " << get_second_argument() << ")";
}
std::string ExpressionPow::to_smt2_string() const {
  return "(pow " + get_first_argument().to_smt2_string() + " " + get_second_argument().to_smt2_string() + ")";
}

mpq_class ExpressionPow::DoEvaluate(const mpq_class &, const mpq_class &) const {
  throw runtime_error("Not implemented");  // Because of mpq_class
#if 0
  check_domain(v1, v2);
  return std::pow(v1, v2);
#endif
}

ExpressionSin::ExpressionSin(const Expression &e) : UnaryExpressionCell{ExpressionKind::Sin, e, false} {}

Expression ExpressionSin::Expand() {
  const Expression &arg{get_argument()};
  const Expression arg_expanded{arg.Expand()};
  if (!arg.EqualTo(arg_expanded)) {
    return sin(arg_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionSin::Substitute(const ExpressionSubstitution &expr_subst,
                                     const FormulaSubstitution &formula_subst) {
  const Expression &arg{get_argument()};
  const Expression arg_subst{arg.Substitute(expr_subst, formula_subst)};
  if (!arg.EqualTo(arg_subst)) {
    return sin(arg_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionSin::Differentiate(const Variable &x) const {
  // ∂/∂x (sin f) = (cos f) * (∂/∂x f)
  const Expression &f{get_argument()};
  return cos(f) * f.Differentiate(x);
}

ostream &ExpressionSin::Display(ostream &os) const { return os << "sin(" << get_argument() << ")"; }
std::string ExpressionSin::to_smt2_string() const { return "(sin " + get_argument().to_smt2_string() + ")"; }

mpq_class ExpressionSin::DoEvaluate(const mpq_class &) const {
  throw runtime_error("Not implemented");  // Because of mpq_class
  // return std::sin(v);
}

ExpressionCos::ExpressionCos(const Expression &e) : UnaryExpressionCell{ExpressionKind::Cos, e, false} {}

Expression ExpressionCos::Expand() {
  const Expression &arg{get_argument()};
  const Expression arg_expanded{arg.Expand()};
  if (!arg.EqualTo(arg_expanded)) {
    return cos(arg_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionCos::Substitute(const ExpressionSubstitution &expr_subst,
                                     const FormulaSubstitution &formula_subst) {
  const Expression &arg{get_argument()};
  const Expression arg_subst{arg.Substitute(expr_subst, formula_subst)};
  if (!arg.EqualTo(arg_subst)) {
    return cos(arg_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionCos::Differentiate(const Variable &x) const {
  // ∂/∂x (cos f) = - (sin f) * (∂/∂x f)
  const Expression &f{get_argument()};
  return -sin(f) * f.Differentiate(x);
}

ostream &ExpressionCos::Display(ostream &os) const { return os << "cos(" << get_argument() << ")"; }
std::string ExpressionCos::to_smt2_string() const { return "(cos " + get_argument().to_smt2_string() + ")"; }

mpq_class ExpressionCos::DoEvaluate(const mpq_class &) const {
  throw runtime_error("Not implemented");  // Because of mpq_class
  // return std::cos(v);
}

ExpressionTan::ExpressionTan(const Expression &e) : UnaryExpressionCell{ExpressionKind::Tan, e, false} {}

Expression ExpressionTan::Expand() {
  const Expression &arg{get_argument()};
  const Expression arg_expanded{arg.Expand()};
  if (!arg.EqualTo(arg_expanded)) {
    return tan(arg_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionTan::Substitute(const ExpressionSubstitution &expr_subst,
                                     const FormulaSubstitution &formula_subst) {
  const Expression &arg{get_argument()};
  const Expression arg_subst{arg.Substitute(expr_subst, formula_subst)};
  if (!arg.EqualTo(arg_subst)) {
    return tan(arg_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionTan::Differentiate(const Variable &x) const {
  // ∂/∂x (tan f) = (1 / (cos f)^2) * (∂/∂x f)
  const Expression &f{get_argument()};
  return (1 / pow(cos(f), 2)) * f.Differentiate(x);
}

ostream &ExpressionTan::Display(ostream &os) const { return os << "tan(" << get_argument() << ")"; }
std::string ExpressionTan::to_smt2_string() const { return "(tan " + get_argument().to_smt2_string() + ")"; }

mpq_class ExpressionTan::DoEvaluate(const mpq_class &) const {
  throw runtime_error("Not implemented");  // Because of mpq_class
  // return std::tan(v);
}

ExpressionAsin::ExpressionAsin(const Expression &e) : UnaryExpressionCell{ExpressionKind::Asin, e, false} {}

void ExpressionAsin::check_domain(const mpq_class &v) {
  if (!((v >= -1.0) && (v <= 1.0))) {
    ostringstream oss;
    oss << "asin(" << v << ") : numerical argument out of domain. " << v << " is not in [-1.0, +1.0]" << endl;
    throw domain_error(oss.str());
  }
}

Expression ExpressionAsin::Expand() {
  const Expression &arg{get_argument()};
  const Expression arg_expanded{arg.Expand()};
  if (!arg.EqualTo(arg_expanded)) {
    return asin(arg_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionAsin::Substitute(const ExpressionSubstitution &expr_subst,
                                      const FormulaSubstitution &formula_subst) {
  const Expression &arg{get_argument()};
  const Expression arg_subst{arg.Substitute(expr_subst, formula_subst)};
  if (!arg.EqualTo(arg_subst)) {
    return asin(arg_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionAsin::Differentiate(const Variable &x) const {
  // ∂/∂x (asin f) = (1 / sqrt(1 - f^2)) (∂/∂x f)
  const Expression &f{get_argument()};
  return (1 / sqrt(1 - pow(f, 2))) * f.Differentiate(x);
}

ostream &ExpressionAsin::Display(ostream &os) const { return os << "asin(" << get_argument() << ")"; }
std::string ExpressionAsin::to_smt2_string() const { return "(asin " + get_argument().to_smt2_string() + ")"; }

mpq_class ExpressionAsin::DoEvaluate(const mpq_class &) const {
  throw runtime_error("Not implemented");  // Because of mpq_class
#if 0
  check_domain(v);
  return std::asin(v);
#endif
}

ExpressionAcos::ExpressionAcos(const Expression &e) : UnaryExpressionCell{ExpressionKind::Acos, e, false} {}

void ExpressionAcos::check_domain(const mpq_class &v) {
  if (!((v >= -1.0) && (v <= 1.0))) {
    ostringstream oss;
    oss << "acos(" << v << ") : numerical argument out of domain. " << v << " is not in [-1.0, +1.0]" << endl;
    throw domain_error(oss.str());
  }
}

Expression ExpressionAcos::Expand() {
  const Expression &arg{get_argument()};
  const Expression arg_expanded{arg.Expand()};
  if (!arg.EqualTo(arg_expanded)) {
    return acos(arg_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionAcos::Substitute(const ExpressionSubstitution &expr_subst,
                                      const FormulaSubstitution &formula_subst) {
  const Expression &arg{get_argument()};
  const Expression arg_subst{arg.Substitute(expr_subst, formula_subst)};
  if (!arg.EqualTo(arg_subst)) {
    return acos(arg_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionAcos::Differentiate(const Variable &x) const {
  // ∂/∂x (acos f) = - 1 / sqrt(1 - f^2) * (∂/∂x f)
  const Expression &f{get_argument()};
  return -1 / sqrt(1 - pow(f, 2)) * f.Differentiate(x);
}

ostream &ExpressionAcos::Display(ostream &os) const { return os << "acos(" << get_argument() << ")"; }
std::string ExpressionAcos::to_smt2_string() const { return "(acos " + get_argument().to_smt2_string() + ")"; }

mpq_class ExpressionAcos::DoEvaluate(const mpq_class &) const {
  throw runtime_error("Not implemented");  // Because of mpq_class
#if 0
  check_domain(v);
  return std::acos(v);
#endif
}

ExpressionAtan::ExpressionAtan(const Expression &e) : UnaryExpressionCell{ExpressionKind::Atan, e, false} {}

Expression ExpressionAtan::Expand() {
  const Expression &arg{get_argument()};
  const Expression arg_expanded{arg.Expand()};
  if (!arg.EqualTo(arg_expanded)) {
    return atan(arg_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionAtan::Substitute(const ExpressionSubstitution &expr_subst,
                                      const FormulaSubstitution &formula_subst) {
  const Expression &arg{get_argument()};
  const Expression arg_subst{arg.Substitute(expr_subst, formula_subst)};
  if (!arg.EqualTo(arg_subst)) {
    return atan(arg_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionAtan::Differentiate(const Variable &x) const {
  // ∂/∂x (atan f) = (1 / (1 + f^2)) * ∂/∂x f
  const Expression &f{get_argument()};
  return (1 / (1 + pow(f, 2))) * f.Differentiate(x);
}

ostream &ExpressionAtan::Display(ostream &os) const { return os << "atan(" << get_argument() << ")"; }
std::string ExpressionAtan::to_smt2_string() const { return "(atan " + get_argument().to_smt2_string() + ")"; }

mpq_class ExpressionAtan::DoEvaluate(const mpq_class &) const {
  throw runtime_error("Not implemented");  // Because of mpq_class
  // return std::atan(v);
}

ExpressionAtan2::ExpressionAtan2(const Expression &e1, const Expression &e2)
    : BinaryExpressionCell{ExpressionKind::Atan2, e1, e2, false} {}

Expression ExpressionAtan2::Expand() {
  const Expression &arg1{get_first_argument()};
  const Expression &arg2{get_second_argument()};
  const Expression arg1_expanded{arg1.Expand()};
  const Expression arg2_expanded{arg2.Expand()};
  if (!arg1.EqualTo(arg1_expanded) || !arg2.EqualTo(arg2_expanded)) {
    return atan2(arg1_expanded, arg2_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionAtan2::Substitute(const ExpressionSubstitution &expr_subst,
                                       const FormulaSubstitution &formula_subst) {
  const Expression &arg1{get_first_argument()};
  const Expression &arg2{get_second_argument()};
  const Expression arg1_subst{arg1.Substitute(expr_subst, formula_subst)};
  const Expression arg2_subst{arg2.Substitute(expr_subst, formula_subst)};
  if (!arg1.EqualTo(arg1_subst) || !arg2.EqualTo(arg2_subst)) {
    return atan2(arg1_subst, arg2_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionAtan2::Differentiate(const Variable &x) const {
  // ∂/∂x (atan2(f,g)) = (g * (∂/∂x f) - f * (∂/∂x g)) / (f^2 + g^2)
  const Expression &f{get_first_argument()};
  const Expression &g{get_second_argument()};
  return (g * f.Differentiate(x) - f * g.Differentiate(x)) / (pow(f, 2) + pow(g, 2));
}

ostream &ExpressionAtan2::Display(ostream &os) const {
  return os << "atan2(" << get_first_argument() << ", " << get_second_argument() << ")";
}
std::string ExpressionAtan2::to_smt2_string() const {
  return "(atan2 " + get_first_argument().to_smt2_string() + " " + get_second_argument().to_smt2_string() + ")";
}

mpq_class ExpressionAtan2::DoEvaluate(const mpq_class &, const mpq_class &) const {
  throw runtime_error("Not implemented");  // Because of mpq_class
  // return std::atan2(v1, v2);
}

ExpressionSinh::ExpressionSinh(const Expression &e) : UnaryExpressionCell{ExpressionKind::Sinh, e, false} {}

Expression ExpressionSinh::Expand() {
  const Expression &arg{get_argument()};
  const Expression arg_expanded{arg.Expand()};
  if (!arg.EqualTo(arg_expanded)) {
    return sinh(arg_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionSinh::Substitute(const ExpressionSubstitution &expr_subst,
                                      const FormulaSubstitution &formula_subst) {
  const Expression &arg{get_argument()};
  const Expression arg_subst{arg.Substitute(expr_subst, formula_subst)};
  if (!arg.EqualTo(arg_subst)) {
    return sinh(arg_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionSinh::Differentiate(const Variable &x) const {
  // ∂/∂x (sinh f) = cosh(f) * (∂/∂x f)
  const Expression &f{get_argument()};
  return cosh(f) * f.Differentiate(x);
}

ostream &ExpressionSinh::Display(ostream &os) const { return os << "sinh(" << get_argument() << ")"; }
std::string ExpressionSinh::to_smt2_string() const { return "(sinh " + get_argument().to_smt2_string() + ")"; }

mpq_class ExpressionSinh::DoEvaluate(const mpq_class &) const {
  throw runtime_error("Not implemented");  // Because of mpq_class
  // return std::sinh(v);
}

ExpressionCosh::ExpressionCosh(const Expression &e) : UnaryExpressionCell{ExpressionKind::Cosh, e, false} {}

Expression ExpressionCosh::Expand() {
  const Expression &arg{get_argument()};
  const Expression arg_expanded{arg.Expand()};
  if (!arg.EqualTo(arg_expanded)) {
    return cosh(arg_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionCosh::Substitute(const ExpressionSubstitution &expr_subst,
                                      const FormulaSubstitution &formula_subst) {
  const Expression &arg{get_argument()};
  const Expression arg_subst{arg.Substitute(expr_subst, formula_subst)};
  if (!arg.EqualTo(arg_subst)) {
    return cosh(arg_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionCosh::Differentiate(const Variable &x) const {
  // ∂/∂x (cosh f) = sinh(f) * (∂/∂x f)
  const Expression &f{get_argument()};
  return sinh(f) * f.Differentiate(x);
}

ostream &ExpressionCosh::Display(ostream &os) const { return os << "cosh(" << get_argument() << ")"; }
std::string ExpressionCosh::to_smt2_string() const { return "(cosh " + get_argument().to_smt2_string() + ")"; }

mpq_class ExpressionCosh::DoEvaluate(const mpq_class &) const {
  throw runtime_error("Not implemented");  // Because of mpq_class
  // return std::cosh(v);
}

ExpressionTanh::ExpressionTanh(const Expression &e) : UnaryExpressionCell{ExpressionKind::Tanh, e, false} {}

Expression ExpressionTanh::Expand() {
  const Expression &arg{get_argument()};
  const Expression arg_expanded{arg.Expand()};
  if (!arg.EqualTo(arg_expanded)) {
    return tanh(arg_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionTanh::Substitute(const ExpressionSubstitution &expr_subst,
                                      const FormulaSubstitution &formula_subst) {
  const Expression &arg{get_argument()};
  const Expression arg_subst{arg.Substitute(expr_subst, formula_subst)};
  if (!arg.EqualTo(arg_subst)) {
    return tanh(arg_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionTanh::Differentiate(const Variable &x) const {
  // ∂/∂x (tanh f) = 1 / (cosh^2(f)) * (∂/∂x f)
  const Expression &f{get_argument()};
  return 1 / pow(cosh(f), 2) * f.Differentiate(x);
}

ostream &ExpressionTanh::Display(ostream &os) const { return os << "tanh(" << get_argument() << ")"; }
std::string ExpressionTanh::to_smt2_string() const { return "(tanh " + get_argument().to_smt2_string() + ")"; }

mpq_class ExpressionTanh::DoEvaluate(const mpq_class &) const {
  throw runtime_error("Not implemented");  // Because of mpq_class
  // return std::tanh(v);
}

ExpressionMin::ExpressionMin(const Expression &e1, const Expression &e2)
    : BinaryExpressionCell{ExpressionKind::Min, e1, e2, false} {}

Expression ExpressionMin::Expand() {
  const Expression &arg1{get_first_argument()};
  const Expression &arg2{get_second_argument()};
  const Expression arg1_expanded{arg1.Expand()};
  const Expression arg2_expanded{arg2.Expand()};
  if (!arg1.EqualTo(arg1_expanded) || !arg2.EqualTo(arg2_expanded)) {
    return min(arg1_expanded, arg2_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionMin::Substitute(const ExpressionSubstitution &expr_subst,
                                     const FormulaSubstitution &formula_subst) {
  const Expression &arg1{get_first_argument()};
  const Expression &arg2{get_second_argument()};
  const Expression arg1_subst{arg1.Substitute(expr_subst, formula_subst)};
  const Expression arg2_subst{arg2.Substitute(expr_subst, formula_subst)};
  if (!arg1.EqualTo(arg1_subst) || !arg2.EqualTo(arg2_subst)) {
    return min(arg1_subst, arg2_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionMin::Differentiate(const Variable &x) const {
  if (GetVariables().include(x)) {
    ostringstream oss;
    Display(oss) << "is not differentiable with respect to " << x << ".";
    throw runtime_error(oss.str());
  } else {
    return Expression::Zero();
  }
}

ostream &ExpressionMin::Display(ostream &os) const {
  return os << "min(" << get_first_argument() << ", " << get_second_argument() << ")";
}
std::string ExpressionMin::to_smt2_string() const {
  return "(min " + get_first_argument().to_smt2_string() + " " + get_second_argument().to_smt2_string() + ")";
}

mpq_class ExpressionMin::DoEvaluate(const mpq_class &v1, const mpq_class &v2) const { return std::min(v1, v2); }

ExpressionMax::ExpressionMax(const Expression &e1, const Expression &e2)
    : BinaryExpressionCell{ExpressionKind::Max, e1, e2, false} {}

Expression ExpressionMax::Expand() {
  const Expression &arg1{get_first_argument()};
  const Expression &arg2{get_second_argument()};
  const Expression arg1_expanded{arg1.Expand()};
  const Expression arg2_expanded{arg2.Expand()};
  if (!arg1.EqualTo(arg1_expanded) || !arg2.EqualTo(arg2_expanded)) {
    return max(arg1_expanded, arg2_expanded);
  } else {
    return GetExpression();
  }
}

Expression ExpressionMax::Substitute(const ExpressionSubstitution &expr_subst,
                                     const FormulaSubstitution &formula_subst) {
  const Expression &arg1{get_first_argument()};
  const Expression &arg2{get_second_argument()};
  const Expression arg1_subst{arg1.Substitute(expr_subst, formula_subst)};
  const Expression arg2_subst{arg2.Substitute(expr_subst, formula_subst)};
  if (!arg1.EqualTo(arg1_subst) || !arg2.EqualTo(arg2_subst)) {
    return max(arg1_subst, arg2_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionMax::Differentiate(const Variable &x) const {
  if (GetVariables().include(x)) {
    ostringstream oss;
    Display(oss) << "is not differentiable with respect to " << x << ".";
    throw runtime_error(oss.str());
  } else {
    return Expression::Zero();
  }
}

ostream &ExpressionMax::Display(ostream &os) const {
  return os << "max(" << get_first_argument() << ", " << get_second_argument() << ")";
}
std::string ExpressionMax::to_smt2_string() const {
  return "(max " + get_first_argument().to_smt2_string() + " " + get_second_argument().to_smt2_string() + ")";
}

mpq_class ExpressionMax::DoEvaluate(const mpq_class &v1, const mpq_class &v2) const { return std::max(v1, v2); }

// ExpressionIfThenElse
// --------------------
ExpressionIfThenElse::ExpressionIfThenElse(const Formula &f_cond, const Expression &e_then, const Expression &e_else)
    : ExpressionCell{ExpressionKind::IfThenElse, false, true},
      f_cond_{f_cond},
      e_then_{e_then},
      e_else_{e_else} {}

void ExpressionIfThenElse::ComputeVariables(std::optional<Variables>& variables) const {
  assert(!variables.has_value());
  variables = Variables{};
  variables.value().insert(f_cond_.GetFreeVariables());
  variables.value().insert(e_then_.GetVariables());
  variables.value().insert(e_else_.GetVariables());
}
void ExpressionIfThenElse::ComputeHash(std::optional<std::size_t>& hash) const {
  assert(!hash.has_value());
  hash = hash_combine(hash_value<Formula>{}(f_cond_), e_then_, e_else_);
}

bool ExpressionIfThenElse::EqualTo(const ExpressionCell &e) const {
  // Expression::EqualTo guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  const ExpressionIfThenElse &ite_e{static_cast<const ExpressionIfThenElse &>(e)};
  return f_cond_.EqualTo(ite_e.f_cond_) && e_then_.EqualTo(ite_e.e_then_) && e_else_.EqualTo(ite_e.e_else_);
}

bool ExpressionIfThenElse::Less(const ExpressionCell &e) const {
  // Expression::Less guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  const ExpressionIfThenElse &ite_e{static_cast<const ExpressionIfThenElse &>(e)};
  if (f_cond_.Less(ite_e.f_cond_)) {
    return true;
  }
  if (ite_e.f_cond_.Less(f_cond_)) {
    return false;
  }
  if (e_then_.Less(ite_e.e_then_)) {
    return true;
  }
  if (ite_e.e_then_.Less(e_then_)) {
    return false;
  }
  return e_else_.Less(ite_e.e_else_);
}

mpq_class ExpressionIfThenElse::Evaluate(const Environment &env) const {
  if (f_cond_.Evaluate(env)) {
    return e_then_.Evaluate(env);
  }
  return e_else_.Evaluate(env);
}

Expression ExpressionIfThenElse::Expand() {
  // TODO(soonho): use the following line when Formula::Expand() is implemented.
  // return if_then_else(f_cond_.Expand(), e_then_.Expand(), e_else_.Expand());
  throw runtime_error("Not yet implemented.");
}

Expression ExpressionIfThenElse::Substitute(const ExpressionSubstitution &expr_subst,
                                            const FormulaSubstitution &formula_subst) {
  const Formula f_cond_subst{f_cond_.Substitute(expr_subst, formula_subst)};
  const Expression e_then_subst{e_then_.Substitute(expr_subst, formula_subst)};
  const Expression e_else_subst{e_else_.Substitute(expr_subst, formula_subst)};
  if (!f_cond_.EqualTo(f_cond_subst) || !e_then_.EqualTo(e_then_subst) || !e_else_.EqualTo(e_else_subst)) {
    return if_then_else(f_cond_subst, e_then_subst, e_else_subst);
  } else {
    return GetExpression();
  }
}

Expression ExpressionIfThenElse::Differentiate(const Variable &x) const {
  if (GetVariables().include(x)) {
    ostringstream oss;
    Display(oss) << "is not differentiable with respect to " << x << ".";
    throw runtime_error(oss.str());
  } else {
    return Expression::Zero();
  }
}

ostream &ExpressionIfThenElse::Display(ostream &os) const {
  return os << "(if " << f_cond_ << " then " << e_then_ << " else " << e_else_ << ")";
}
std::string ExpressionIfThenElse::to_smt2_string() const {
  return "(ite " + f_cond_.to_smt2_string() + " " + e_then_.to_smt2_string() + " " + e_else_.to_smt2_string() + ")";
}

// ExpressionUninterpretedFunction
// --------------------
ExpressionUninterpretedFunction::ExpressionUninterpretedFunction(const string &name, const Variables &vars)
    : ExpressionCell{ExpressionKind::UninterpretedFunction, false, false, vars},
      name_{name},
      variables_{vars} {}

void ExpressionUninterpretedFunction::ComputeHash(std::optional<size_t>& hash) const {
  assert(!hash.has_value());
  hash = hash_combine(hash_value<string>{}(name_), variables_);
}

bool ExpressionUninterpretedFunction::EqualTo(const ExpressionCell &e) const {
  // Expression::EqualTo guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  const ExpressionUninterpretedFunction &uf_e{static_cast<const ExpressionUninterpretedFunction &>(e)};
  return name_ == uf_e.name_ && variables_ == uf_e.variables_;
}

bool ExpressionUninterpretedFunction::Less(const ExpressionCell &e) const {
  // Expression::Less guarantees the following assertion.
  assert(get_kind() == e.get_kind());
  const ExpressionUninterpretedFunction &uf_e{static_cast<const ExpressionUninterpretedFunction &>(e)};
  if (name_ < uf_e.name_) {
    return true;
  }
  if (uf_e.name_ < name_) {
    return false;
  }
  return variables_ < uf_e.variables_;
}

mpq_class ExpressionUninterpretedFunction::Evaluate(const Environment &) const {
  throw runtime_error("Uninterpreted-function expression cannot be evaluated.");
}

Expression ExpressionUninterpretedFunction::Expand() { return GetExpression(); }

Expression ExpressionUninterpretedFunction::Substitute(const ExpressionSubstitution &expr_subst,
                                                       const FormulaSubstitution &formula_subst) {
  // This method implements the following substitution:
  //     uf(name, {v₁, ..., vₙ}).Substitute(expr_subst, formula_subst)
  //   = uf(name, ⋃ᵢ (expr_subst[vᵢ].GetVariables() ∪ formula_subst[vᵢ])
  //
  // For example, we have:
  //     uf("uf1", {x, y, b}).Substitute({x ↦ 1, y ↦ y + z}, {b ↦ x > 0})
  //   = uf("uf1", ∅ ∪ {y, z} ∪ {x})
  //   = uf("uf1", {x, y, z}).
  Variables new_vars;
  for (const auto &var : variables_) {
    if (var.get_type() == Variable::Type::BOOLEAN) {
      if (formula_subst.count(var) > 0) {
        new_vars += formula_subst.at(var).GetFreeVariables();
      }
    } else {
      if (expr_subst.count(var) > 0) {
        new_vars += expr_subst.at(var).GetVariables();
      }
    }
  }
  return uninterpreted_function(name_, new_vars);
}

Expression ExpressionUninterpretedFunction::Differentiate(const Variable &x) const {
  if (variables_.include(x)) {
    // This uninterpreted function does have `x` as an argument, but we don't
    // have sufficient information to differentiate it with respect to `x`.
    ostringstream oss;
    oss << "Uninterpreted-function expression ";
    Display(oss);
    oss << " is not differentiable with respect to " << x << ".";
    throw runtime_error(oss.str());
  } else {
    // `x` is free in this uninterpreted function.
    return Expression::Zero();
  }
}

ostream &ExpressionUninterpretedFunction::Display(ostream &os) const { return os << name_ << "(" << variables_ << ")"; }
std::string ExpressionUninterpretedFunction::to_smt2_string() const {
  ostringstream oss;
  oss << name_;
  if (!variables_.empty()) {
    oss << " (";
    for (const auto &var : variables_) {
      oss << var.to_string() << " ";
    }
    oss << ")";
  }
  return oss.str();
}

bool is_constant(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Constant; }
bool is_infinite(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Infty; }
bool is_variable(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Var; }
bool is_addition(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Add; }
bool is_multiplication(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Mul; }
bool is_division(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Div; }
bool is_log(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Log; }
bool is_abs(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Abs; }
bool is_exp(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Exp; }
bool is_sqrt(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Sqrt; }
bool is_pow(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Pow; }
bool is_sin(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Sin; }
bool is_cos(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Cos; }
bool is_tan(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Tan; }
bool is_asin(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Asin; }
bool is_acos(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Acos; }
bool is_atan(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Atan; }
bool is_atan2(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Atan2; }
bool is_sinh(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Sinh; }
bool is_cosh(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Cosh; }
bool is_tanh(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Tanh; }
bool is_min(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Min; }
bool is_max(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::Max; }
bool is_if_then_else(const ExpressionCell &c) { return c.get_kind() == ExpressionKind::IfThenElse; }
bool is_uninterpreted_function(const ExpressionCell &c) {
  return c.get_kind() == ExpressionKind::UninterpretedFunction;
}

const ExpressionConstant *to_constant(const ExpressionCell *const expr_ptr) {
  assert(is_constant(*expr_ptr));
  return static_cast<const ExpressionConstant *>(expr_ptr);
}
const ExpressionConstant *to_constant(const Expression &e) { return to_constant(e.ptr_); }

const ExpressionInfty *to_infty(const ExpressionCell *const expr_ptr) {
  assert(is_infinite(*expr_ptr));
  return static_cast<const ExpressionInfty *>(expr_ptr);
}
const ExpressionInfty *to_infty(const Expression &e) { return to_infty(e.ptr_); }

const ExpressionVar *to_variable(const ExpressionCell *const expr_ptr) {
  assert(is_variable(*expr_ptr));
  return static_cast<const ExpressionVar *>(expr_ptr);
}
const ExpressionVar *to_variable(const Expression &e) { return to_variable(e.ptr_); }

const UnaryExpressionCell *to_unary(const ExpressionCell *const expr_ptr) {
  assert(is_log(*expr_ptr) || is_abs(*expr_ptr) || is_exp(*expr_ptr) || is_sqrt(*expr_ptr) || is_sin(*expr_ptr) ||
         is_cos(*expr_ptr) || is_tan(*expr_ptr) || is_asin(*expr_ptr) || is_acos(*expr_ptr) || is_atan(*expr_ptr) ||
         is_sinh(*expr_ptr) || is_cosh(*expr_ptr) || is_tanh(*expr_ptr));
  return static_cast<const UnaryExpressionCell *>(expr_ptr);
}
const UnaryExpressionCell *to_unary(const Expression &e) { return to_unary(e.ptr_); }

const BinaryExpressionCell *to_binary(const ExpressionCell *const expr_ptr) {
  assert(is_division(*expr_ptr) || is_pow(*expr_ptr) || is_atan2(*expr_ptr) || is_min(*expr_ptr) || is_max(*expr_ptr));
  return static_cast<const BinaryExpressionCell *>(expr_ptr);
}
const BinaryExpressionCell *to_binary(const Expression &e) { return to_binary(e.ptr_); }

const ExpressionAdd *to_addition(const ExpressionCell *const expr_ptr) {
  assert(is_addition(*expr_ptr));
  return static_cast<const ExpressionAdd *>(expr_ptr);
}
const ExpressionAdd *to_addition(const Expression &e) { return to_addition(e.ptr_); }
ExpressionAdd *to_addition(ExpressionCell *expr_ptr) {
  assert(is_addition(*expr_ptr));
  return static_cast<ExpressionAdd *>(expr_ptr);
}
ExpressionAdd *to_addition(Expression &e) { return to_addition(e.ptr_); }

const ExpressionMul *to_multiplication(const ExpressionCell *const expr_ptr) {
  assert(is_multiplication(*expr_ptr));
  return static_cast<const ExpressionMul *>(expr_ptr);
}
const ExpressionMul *to_multiplication(const Expression &e) { return to_multiplication(e.ptr_); }
ExpressionMul *to_multiplication(ExpressionCell *const expr_ptr) {
  assert(is_multiplication(*expr_ptr));
  return static_cast<ExpressionMul *>(expr_ptr);
}
ExpressionMul *to_multiplication(Expression &e) { return to_multiplication(e.ptr_); }

const ExpressionDiv *to_division(const ExpressionCell *const expr_ptr) {
  assert(is_division(*expr_ptr));
  return static_cast<const ExpressionDiv *>(expr_ptr);
}
const ExpressionDiv *to_division(const Expression &e) { return to_division(e.ptr_); }

const ExpressionLog *to_log(const ExpressionCell *const expr_ptr) {
  assert(is_log(*expr_ptr));
  return static_cast<const ExpressionLog *>(expr_ptr);
}
const ExpressionLog *to_log(const Expression &e) { return to_log(e.ptr_); }

const ExpressionAbs *to_abs(const ExpressionCell *const expr_ptr) {
  assert(is_abs(*expr_ptr));
  return static_cast<const ExpressionAbs *>(expr_ptr);
}
const ExpressionAbs *to_abs(const Expression &e) { return to_abs(e.ptr_); }

const ExpressionExp *to_exp(const ExpressionCell *const expr_ptr) {
  assert(is_exp(*expr_ptr));
  return static_cast<const ExpressionExp *>(expr_ptr);
}
const ExpressionExp *to_exp(const Expression &e) { return to_exp(e.ptr_); }

const ExpressionSqrt *to_sqrt(const ExpressionCell *const expr_ptr) {
  assert(is_sqrt(*expr_ptr));
  return static_cast<const ExpressionSqrt *>(expr_ptr);
}
const ExpressionSqrt *to_sqrt(const Expression &e) { return to_sqrt(e.ptr_); }
const ExpressionPow *to_pow(const ExpressionCell *const expr_ptr) {
  assert(is_pow(*expr_ptr));
  return static_cast<const ExpressionPow *>(expr_ptr);
}
const ExpressionPow *to_pow(const Expression &e) { return to_pow(e.ptr_); }

const ExpressionSin *to_sin(const ExpressionCell *const expr_ptr) {
  assert(is_sin(*expr_ptr));
  return static_cast<const ExpressionSin *>(expr_ptr);
}
const ExpressionSin *to_sin(const Expression &e) { return to_sin(e.ptr_); }

const ExpressionCos *to_cos(const ExpressionCell *const expr_ptr) {
  assert(is_cos(*expr_ptr));
  return static_cast<const ExpressionCos *>(expr_ptr);
}
const ExpressionCos *to_cos(const Expression &e) { return to_cos(e.ptr_); }

const ExpressionTan *to_tan(const ExpressionCell *const expr_ptr) {
  assert(is_tan(*expr_ptr));
  return static_cast<const ExpressionTan *>(expr_ptr);
}
const ExpressionTan *to_tan(const Expression &e) { return to_tan(e.ptr_); }

const ExpressionAsin *to_asin(const ExpressionCell *const expr_ptr) {
  assert(is_asin(*expr_ptr));
  return static_cast<const ExpressionAsin *>(expr_ptr);
}
const ExpressionAsin *to_asin(const Expression &e) { return to_asin(e.ptr_); }

const ExpressionAcos *to_acos(const ExpressionCell *const expr_ptr) {
  assert(is_acos(*expr_ptr));
  return static_cast<const ExpressionAcos *>(expr_ptr);
}
const ExpressionAcos *to_acos(const Expression &e) { return to_acos(e.ptr_); }

const ExpressionAtan *to_atan(const ExpressionCell *const expr_ptr) {
  assert(is_atan(*expr_ptr));
  return static_cast<const ExpressionAtan *>(expr_ptr);
}
const ExpressionAtan *to_atan(const Expression &e) { return to_atan(e.ptr_); }

const ExpressionAtan2 *to_atan2(const ExpressionCell *const expr_ptr) {
  assert(is_atan2(*expr_ptr));
  return static_cast<const ExpressionAtan2 *>(expr_ptr);
}
const ExpressionAtan2 *to_atan2(const Expression &e) { return to_atan2(e.ptr_); }

const ExpressionSinh *to_sinh(const ExpressionCell *const expr_ptr) {
  assert(is_sinh(*expr_ptr));
  return static_cast<const ExpressionSinh *>(expr_ptr);
}
const ExpressionSinh *to_sinh(const Expression &e) { return to_sinh(e.ptr_); }

const ExpressionCosh *to_cosh(const ExpressionCell *const expr_ptr) {
  assert(is_cosh(*expr_ptr));
  return static_cast<const ExpressionCosh *>(expr_ptr);
}
const ExpressionCosh *to_cosh(const Expression &e) { return to_cosh(e.ptr_); }

const ExpressionTanh *to_tanh(const ExpressionCell *const expr_ptr) {
  assert(is_tanh(*expr_ptr));
  return static_cast<const ExpressionTanh *>(expr_ptr);
}
const ExpressionTanh *to_tanh(const Expression &e) { return to_tanh(e.ptr_); }

const ExpressionMin *to_min(const ExpressionCell *const expr_ptr) {
  assert(is_min(*expr_ptr));
  return static_cast<const ExpressionMin *>(expr_ptr);
}
const ExpressionMin *to_min(const Expression &e) { return to_min(e.ptr_); }

const ExpressionMax *to_max(const ExpressionCell *const expr_ptr) {
  assert(is_max(*expr_ptr));
  return static_cast<const ExpressionMax *>(expr_ptr);
}
const ExpressionMax *to_max(const Expression &e) { return to_max(e.ptr_); }

const ExpressionIfThenElse *to_if_then_else(const ExpressionCell *const expr_ptr) {
  assert(is_if_then_else(*expr_ptr));
  return static_cast<const ExpressionIfThenElse *>(expr_ptr);
}
const ExpressionIfThenElse *to_if_then_else(const Expression &e) { return to_if_then_else(e.ptr_); }

const ExpressionUninterpretedFunction *to_uninterpreted_function(const ExpressionCell *const expr_ptr) {
  assert(is_uninterpreted_function(*expr_ptr));
  return static_cast<const ExpressionUninterpretedFunction *>(expr_ptr);
}
const ExpressionUninterpretedFunction *to_uninterpreted_function(const Expression &e) {
  return to_uninterpreted_function(e.ptr_);
}

}  // namespace dlinear::drake::symbolic
