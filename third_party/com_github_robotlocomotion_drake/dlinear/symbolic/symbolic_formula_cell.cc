#include "dlinear/symbolic/symbolic_formula_cell.h"

#include <algorithm>
#include <cassert>
#include <iostream>
#include <memory>
#include <set>
#include <sstream>
#include <stdexcept>

#include "dlinear/symbolic/hash.h"
#include "dlinear/symbolic/symbolic_environment.h"
#include "dlinear/symbolic/symbolic_expression.h"
#include "dlinear/symbolic/symbolic_formula.h"
#include "dlinear/symbolic/symbolic_variable.h"
#include "dlinear/symbolic/symbolic_variables.h"

namespace dlinear::drake::symbolic {

using std::any_of;
using std::equal;
using std::hash;
using std::lexicographical_compare;
using std::ostream;
using std::ostringstream;
using std::runtime_error;
using std::set;
using std::string;

FormulaCell::FormulaCell(const FormulaKind k, const size_t hash, const bool include_ite)
    : variables_{},
      kind_{k},
      hash_{hash_combine(hash, static_cast<size_t>(kind_))},
      include_ite_{include_ite} {}

Formula FormulaCell::GetFormula() { return Formula{this}; }

const Variables &FormulaCell::GetFreeVariables() {
  if (variables_.empty()) ExtractFreeVariables();
  return variables_;
}

bool FormulaCell::include_ite() const { return include_ite_; }

RelationalFormulaCell::RelationalFormulaCell(const FormulaKind k,
                                             const Expression &lhs,
                                             const Expression &rhs)
    : FormulaCell{k, hash_combine(lhs.get_hash(), rhs),
                  lhs.include_ite() || rhs.include_ite()},
      e_lhs_{lhs},
      e_rhs_{rhs} {}

bool RelationalFormulaCell::EqualTo(const FormulaCell &f) const {
  // Formula::EqualTo guarantees the following assertion.
  assert(get_kind() == f.get_kind());
  const auto &rel_f = static_cast<const RelationalFormulaCell &>(f);
  return e_lhs_.EqualTo(rel_f.e_lhs_) && e_rhs_.EqualTo(rel_f.e_rhs_);
}

bool RelationalFormulaCell::Less(const FormulaCell &f) const {
  // Formula::Less guarantees the following assertion.
  assert(get_kind() == f.get_kind());
  const auto &rel_f = static_cast<const RelationalFormulaCell &>(f);
  if (e_lhs_.Less(rel_f.e_lhs_)) {
    return true;
  }
  if (rel_f.e_lhs_.Less(e_lhs_)) {
    return false;
  }
  return e_rhs_.Less(rel_f.e_rhs_);
}

void RelationalFormulaCell::ExtractFreeVariables() {
  assert(variables_.empty());
  variables_ = e_lhs_.GetVariables() + e_rhs_.GetVariables();
}

NaryFormulaCell::NaryFormulaCell(const FormulaKind k, set<Formula> formulas)
    : FormulaCell{k, hash_value < set<Formula>>{}(formulas),
any_of(formulas.begin(), formulas.end(),
[](const Formula& f) { return f.include_ite(); })},
      formulas_{std::move(formulas)} {}

void NaryFormulaCell::ExtractFreeVariables() {
  assert(variables_.empty());
  for (const auto &f : formulas_) {
    variables_.insert(f.GetFreeVariables());
  }
}

bool NaryFormulaCell::EqualTo(const FormulaCell &f) const {
  // Formula::EqualTo guarantees the following assertion.
  assert(get_kind() == f.get_kind());
  const auto &nary_f = static_cast<const NaryFormulaCell &>(f);
  return equal(
      formulas_.cbegin(), formulas_.cend(), nary_f.formulas_.cbegin(),
      nary_f.formulas_.cend(),
      [](const Formula &f1, const Formula &f2) { return f1.EqualTo(f2); });
}

bool NaryFormulaCell::Less(const FormulaCell &f) const {
  // Formula::Less guarantees the following assertion.
  assert(get_kind() == f.get_kind());
  const auto &nary_f = static_cast<const NaryFormulaCell &>(f);
  return lexicographical_compare(
      formulas_.cbegin(), formulas_.cend(), nary_f.formulas_.cbegin(),
      nary_f.formulas_.cend(),
      [](const Formula &f1, const Formula &f2) { return f1.Less(f2); });
}

ostream &NaryFormulaCell::DisplayWithOp(ostream &os, const string &op) const {
  const set<Formula> &formulas{get_operands()};
  auto it(formulas.cbegin());
  assert(formulas.size() > 1U);
  os << "(";
  os << *it;
  ++it;
  while (it != formulas.cend()) {
    os << " " << op << " " << *it;
    ++it;
  }
  os << ")";
  return os;
}

FormulaTrue::FormulaTrue()
    : FormulaCell{FormulaKind::True, hash<string>{}("True"), false} {}

bool FormulaTrue::EqualTo([[maybe_unused]] const FormulaCell &f) const {
  // Formula::EqualTo guarantees the following assertion.
  assert(get_kind() == f.get_kind());
  return true;  // There is only one instance of this kind.
}

bool FormulaTrue::Less([[maybe_unused]] const FormulaCell &f) const {
  // Formula::Less guarantees the following assertion.
  assert(get_kind() == f.get_kind());
  // True < True ==> false
  return false;
}

bool FormulaTrue::Evaluate(const Environment &) const { return true; }

Formula FormulaTrue::Substitute(const ExpressionSubstitution &,
                                const FormulaSubstitution &) {
  return Formula::True();
}

ostream &FormulaTrue::Display(ostream &os) const { return os << "True"; }
std::string FormulaTrue::to_smt2_string() const { return "(true)"; }

FormulaFalse::FormulaFalse()
    : FormulaCell{FormulaKind::False, hash<string>{}("False"), false} {}

bool FormulaFalse::EqualTo([[maybe_unused]] const FormulaCell &f) const {
  // Formula::EqualTo guarantees the following assertion.
  assert(get_kind() == f.get_kind());
  return true;  // There is only one instance of this kind.
}

bool FormulaFalse::Less([[maybe_unused]] const FormulaCell &f) const {
  // Formula::Less guarantees the following assertion.
  assert(get_kind() == f.get_kind());
  // False < False ==> false
  return false;
}

bool FormulaFalse::Evaluate(const Environment &) const { return false; }

Formula FormulaFalse::Substitute(const ExpressionSubstitution &,
                                 const FormulaSubstitution &) {
  return Formula::False();
}

ostream &FormulaFalse::Display(ostream &os) const { return os << "False"; }
std::string FormulaFalse::to_smt2_string() const { return "(false)"; }

FormulaVar::FormulaVar(const Variable &v)
    : FormulaCell{FormulaKind::Var, std::hash<Variable>{}(v), false},
      var_{v} {
  // Dummy symbolic variable (ID = 0) should not be used in constructing
  // symbolic formulas.
  if (var_.is_dummy()) {
    throw runtime_error("Dummy variable is used to construct an expression.");
  }
  // Boolean symbolic variable should be used in constructing symbolic
  // formulas.
  if (var_.get_type() != Variable::Type::BOOLEAN) {
    ostringstream oss;
    oss << "Variable " << var_ << " is of type " << var_.get_type()
        << " and it should not be used to construct a "
           "symbolic formula.";
    throw runtime_error(oss.str());
  }
}

void FormulaVar::ExtractFreeVariables() {
  assert(variables_.empty());
  variables_.insert(var_);
}

bool FormulaVar::EqualTo(const FormulaCell &f) const {
  // Formula::EqualTo guarantees the following assertion.
  assert(get_kind() == f.get_kind());
  const FormulaVar &f_var{static_cast<const FormulaVar &>(f)};
  return var_.equal_to(f_var.var_);
}

bool FormulaVar::Less(const FormulaCell &f) const {
  // Formula::Less guarantees the following assertion.
  assert(get_kind() == f.get_kind());
  const FormulaVar &f_var{static_cast<const FormulaVar &>(f)};
  return var_.less(f_var.var_);
}

bool FormulaVar::Evaluate(const Environment &env) const {
    return static_cast<bool>(env.at(var_));
}

Formula FormulaVar::Substitute(const ExpressionSubstitution &,
                               const FormulaSubstitution &formula_subst) {
  const auto it = formula_subst.find(var_);
  if (it != formula_subst.end()) {
    return it->second;
  }
  return GetFormula();
}

ostream &FormulaVar::Display(ostream &os) const { return os << var_; }
std::string FormulaVar::to_smt2_string() const { return var_.get_name(); }

const Variable &FormulaVar::get_variable() const { return var_; }

FormulaEq::FormulaEq(const Expression &e1, const Expression &e2)
    : RelationalFormulaCell{FormulaKind::Eq, e1, e2} {}

namespace {
// Helper function for ExpressionEq::Evaluate and ExpressionNeq::Evaluate.
//
// Checks if `e1.EvaluatePartial(env)` and `e2.EvaluatePartial(env)` are
// structurally equal.
bool CheckStructuralEqualityUptoPartialEvaluation(const Expression &e1,
                                                  const Expression &e2,
                                                  const Environment &env) {
  // Trivial case where env = ∅.
  if (env.empty()) {
    return e1.EqualTo(e2);
  }
  // Since `Expression::Evaluate` is faster than `Expression::EvaluatePartial`,
  // we use:
  //  - `Expression::Evaluate`        if if (vars(e₁) ∪ vars(e₂) ⊆ dom(env).
  //  - `Expression::EvaluatePartial` otherwise.
  const Variables vars{e1.GetVariables() + e2.GetVariables()};
  if (vars.size() <= env.size() && vars.IsSubsetOf(env.domain())) {
    return e1.Evaluate(env) == e2.Evaluate(env);
  } else {
    return e1.EvaluatePartial(env).EqualTo(e2.EvaluatePartial(env));
  }
}
}  // namespace

bool FormulaEq::Evaluate(const Environment &env) const {
  return CheckStructuralEqualityUptoPartialEvaluation(
      get_lhs_expression(), get_rhs_expression(), env);
}

Formula FormulaEq::Substitute(const ExpressionSubstitution &expr_subst,
                              const FormulaSubstitution &formula_subst) {
  const Expression &lhs{get_lhs_expression()};
  const Expression &rhs{get_rhs_expression()};
  const Expression lhs_subst{lhs.Substitute(expr_subst, formula_subst)};
  const Expression rhs_subst{rhs.Substitute(expr_subst, formula_subst)};
  if (!lhs.EqualTo(lhs_subst) || !rhs.EqualTo(rhs_subst)) {
    return lhs_subst == rhs_subst;
  } else {
    return GetFormula();
  }
}

ostream &FormulaEq::Display(ostream &os) const {
  return os << "(" << get_lhs_expression() << " == " << get_rhs_expression()
            << ")";
}
std::string FormulaEq::to_smt2_string() const {
  return "(= " + get_lhs_expression().to_smt2_string() + " " +
      get_rhs_expression().to_smt2_string() + ")";
}

FormulaNeq::FormulaNeq(const Expression &e1, const Expression &e2)
    : RelationalFormulaCell{FormulaKind::Neq, e1, e2} {}

bool FormulaNeq::Evaluate(const Environment &env) const {
  return !CheckStructuralEqualityUptoPartialEvaluation(
      get_lhs_expression(), get_rhs_expression(), env);
}

Formula FormulaNeq::Substitute(const ExpressionSubstitution &expr_subst,
                               const FormulaSubstitution &formula_subst) {
  const Expression &lhs{get_lhs_expression()};
  const Expression &rhs{get_rhs_expression()};
  const Expression lhs_subst{lhs.Substitute(expr_subst, formula_subst)};
  const Expression rhs_subst{rhs.Substitute(expr_subst, formula_subst)};
  if (!lhs.EqualTo(lhs_subst) || !rhs.EqualTo(rhs_subst)) {
    return lhs_subst != rhs_subst;
  } else {
    return GetFormula();
  }
}

ostream &FormulaNeq::Display(ostream &os) const {
  return os << "(" << get_lhs_expression() << " != " << get_rhs_expression()
            << ")";
}
std::string FormulaNeq::to_smt2_string() const {
  return "(not (= " + get_lhs_expression().to_smt2_string() + " " +
         get_rhs_expression().to_smt2_string() + "))";
}

FormulaGt::FormulaGt(const Expression &e1, const Expression &e2)
    : RelationalFormulaCell{FormulaKind::Gt, e1, e2} {}

bool FormulaGt::Evaluate(const Environment &env) const {
  return get_lhs_expression().Evaluate(env) >
      get_rhs_expression().Evaluate(env);
}

Formula FormulaGt::Substitute(const ExpressionSubstitution &expr_subst,
                              const FormulaSubstitution &formula_subst) {
  const Expression &lhs{get_lhs_expression()};
  const Expression &rhs{get_rhs_expression()};
  const Expression lhs_subst{lhs.Substitute(expr_subst, formula_subst)};
  const Expression rhs_subst{rhs.Substitute(expr_subst, formula_subst)};
  if (!lhs.EqualTo(lhs_subst) || !rhs.EqualTo(rhs_subst)) {
    return lhs_subst > rhs_subst;
  } else {
    return GetFormula();
  }
}

ostream &FormulaGt::Display(ostream &os) const {
  return os << "(" << get_lhs_expression() << " > " << get_rhs_expression()
            << ")";
}
std::string FormulaGt::to_smt2_string() const {
  return "(> " + get_lhs_expression().to_smt2_string() + " " +
         get_rhs_expression().to_smt2_string() + ")";
}

FormulaGeq::FormulaGeq(const Expression &e1, const Expression &e2)
    : RelationalFormulaCell{FormulaKind::Geq, e1, e2} {}

bool FormulaGeq::Evaluate(const Environment &env) const {
  return get_lhs_expression().Evaluate(env) >=
      get_rhs_expression().Evaluate(env);
}

Formula FormulaGeq::Substitute(const ExpressionSubstitution &expr_subst,
                               const FormulaSubstitution &formula_subst) {
  const Expression &lhs{get_lhs_expression()};
  const Expression &rhs{get_rhs_expression()};
  const Expression lhs_subst{lhs.Substitute(expr_subst, formula_subst)};
  const Expression rhs_subst{rhs.Substitute(expr_subst, formula_subst)};
  if (!lhs.EqualTo(lhs_subst) || !rhs.EqualTo(rhs_subst)) {
    return lhs_subst >= rhs_subst;
  } else {
    return GetFormula();
  }
}

ostream &FormulaGeq::Display(ostream &os) const {
  return os << "(" << get_lhs_expression() << " >= " << get_rhs_expression()
            << ")";
}
std::string FormulaGeq::to_smt2_string() const {
  return "(>= " + get_lhs_expression().to_smt2_string() + " " +
         get_rhs_expression().to_smt2_string() + ")";
}

FormulaLt::FormulaLt(const Expression &e1, const Expression &e2)
    : RelationalFormulaCell{FormulaKind::Lt, e1, e2} {}

bool FormulaLt::Evaluate(const Environment &env) const {
  return get_lhs_expression().Evaluate(env) <
      get_rhs_expression().Evaluate(env);
}

Formula FormulaLt::Substitute(const ExpressionSubstitution &expr_subst,
                              const FormulaSubstitution &formula_subst) {
  const Expression &lhs{get_lhs_expression()};
  const Expression &rhs{get_rhs_expression()};
  const Expression lhs_subst{lhs.Substitute(expr_subst, formula_subst)};
  const Expression rhs_subst{rhs.Substitute(expr_subst, formula_subst)};
  if (!lhs.EqualTo(lhs_subst) || !rhs.EqualTo(rhs_subst)) {
    return lhs_subst < rhs_subst;
  } else {
    return GetFormula();
  }
}

ostream &FormulaLt::Display(ostream &os) const {
  return os << "(" << get_lhs_expression() << " < " << get_rhs_expression()
            << ")";
}
std::string FormulaLt::to_smt2_string() const {
  return "(< " + get_lhs_expression().to_smt2_string() + " " +
         get_rhs_expression().to_smt2_string() + ")";
}

FormulaLeq::FormulaLeq(const Expression &e1, const Expression &e2)
    : RelationalFormulaCell{FormulaKind::Leq, e1, e2} {}

bool FormulaLeq::Evaluate(const Environment &env) const {
  return get_lhs_expression().Evaluate(env) <=
      get_rhs_expression().Evaluate(env);
}

Formula FormulaLeq::Substitute(const ExpressionSubstitution &expr_subst,
                               const FormulaSubstitution &formula_subst) {
  const Expression &lhs{get_lhs_expression()};
  const Expression &rhs{get_rhs_expression()};
  const Expression lhs_subst{lhs.Substitute(expr_subst, formula_subst)};
  const Expression rhs_subst{rhs.Substitute(expr_subst, formula_subst)};
  if (!lhs.EqualTo(lhs_subst) || !rhs.EqualTo(rhs_subst)) {
    return lhs_subst <= rhs_subst;
  } else {
    return GetFormula();
  }
}

ostream &FormulaLeq::Display(ostream &os) const {
  return os << "(" << get_lhs_expression() << " <= " << get_rhs_expression()
            << ")";
}
std::string FormulaLeq::to_smt2_string() const {
  return "(<= " + get_lhs_expression().to_smt2_string() + " " +
         get_rhs_expression().to_smt2_string() + ")";
}

FormulaAnd::FormulaAnd(set<Formula> formulas)
    : NaryFormulaCell{FormulaKind::And, std::move(formulas)} {
  assert(get_operands().size() > 1U);
}

FormulaAnd::FormulaAnd(const Formula &f1, const Formula &f2)
    : NaryFormulaCell{FormulaKind::And, set<Formula>{f1, f2}} {}

bool FormulaAnd::Evaluate(const Environment &env) const {
  for (const auto &f : get_operands()) {
    if (!f.Evaluate(env)) {
      return false;
    }
  }
  return true;
}

Formula FormulaAnd::Substitute(const ExpressionSubstitution &expr_subst,
                               const FormulaSubstitution &formula_subst) {
  Formula ret{Formula::True()};
  bool changed{false};
  for (const auto &f : get_operands()) {
    const Formula f_subst{f.Substitute(expr_subst, formula_subst)};
    if (!f.EqualTo(f_subst)) {
      ret = ret && f_subst;
      changed = true;
    } else {
      ret = ret && f;
    }
    // short-circuiting
    if (is_false(ret)) {
      return ret;
    }
  }
  if (changed) {
    return ret;
  } else {
    return GetFormula();
  }
}

ostream &FormulaAnd::Display(ostream &os) const {
  return DisplayWithOp(os, "and");
}
std::string FormulaAnd::to_smt2_string() const {
  ostringstream oss;
  oss << "(and";
  for (const auto &f : get_operands()) {
    oss << " " << f.to_smt2_string();
  }
  oss << ")";
  return oss.str();
}

FormulaOr::FormulaOr(set<Formula> formulas)
    : NaryFormulaCell{FormulaKind::Or, std::move(formulas)} {
  assert(get_operands().size() > 1U);
}

FormulaOr::FormulaOr(const Formula &f1, const Formula &f2)
    : NaryFormulaCell{FormulaKind::Or, set<Formula>{f1, f2}} {}

bool FormulaOr::Evaluate(const Environment &env) const {
  for (const auto &f : get_operands()) {
    if (f.Evaluate(env)) {
      return true;
    }
  }
  return false;
}

Formula FormulaOr::Substitute(const ExpressionSubstitution &expr_subst,
                              const FormulaSubstitution &formula_subst) {
  Formula ret{Formula::False()};
  bool changed{false};
  for (const auto &f : get_operands()) {
    const Formula f_subst{f.Substitute(expr_subst, formula_subst)};
    if (!f.EqualTo(f_subst)) {
      ret = ret || f_subst;
      changed = true;
    } else {
      ret = ret || f;
    }
    // short-circuiting
    if (is_true(ret)) {
      return ret;
    }
  }
  if (changed) {
    return ret;
  } else {
    return GetFormula();
  }
}

ostream &FormulaOr::Display(ostream &os) const {
  return DisplayWithOp(os, "or");
}
std::string FormulaOr::to_smt2_string() const {
  ostringstream oss;
  oss << "(or";
  for (const auto &f : get_operands()) {
    oss << " " << f.to_smt2_string();
  }
  oss << ")";
  return oss.str();
}

FormulaNot::FormulaNot(const Formula &f)
    : FormulaCell{FormulaKind::Not, f.get_hash(), f.include_ite()},
      f_{f} {}

void FormulaNot::ExtractFreeVariables() {
    assert(variables_.empty());
    variables_ = f_.GetFreeVariables();
}

bool FormulaNot::EqualTo(const FormulaCell &f) const {
  // Formula::EqualTo guarantees the following assertion.
  assert(get_kind() == f.get_kind());
  const FormulaNot &f_not{static_cast<const FormulaNot &>(f)};
  return f_.EqualTo(f_not.f_);
}

bool FormulaNot::Less(const FormulaCell &f) const {
  // Formula::Less guarantees the following assertion.
  assert(get_kind() == f.get_kind());
  const FormulaNot &not_f{static_cast<const FormulaNot &>(f)};
  return f_.Less(not_f.f_);
}

bool FormulaNot::Evaluate(const Environment &env) const {
  return !f_.Evaluate(env);
}

Formula FormulaNot::Substitute(const ExpressionSubstitution &expr_subst,
                               const FormulaSubstitution &formula_subst) {
  const Formula f_subst{f_.Substitute(expr_subst, formula_subst)};
  if (!f_.EqualTo(f_subst)) {
    return !f_subst;
  } else {
    return GetFormula();
  }
}

ostream &FormulaNot::Display(ostream &os) const {
  return os << "!(" << f_ << ")";
}
std::string FormulaNot::to_smt2_string() const {
  return "(not " + f_.to_smt2_string() + ")";
}

FormulaForall::FormulaForall(const Variables &vars, Formula f)
    : FormulaCell{FormulaKind::Forall, hash_combine(vars.get_hash(), f),
                  f.include_ite()},
      vars_{vars},
      f_{std::move(f)} {}

void FormulaForall::ExtractFreeVariables() {
    assert(variables_.empty());
    variables_ = f_.GetFreeVariables() - vars_;
}

bool FormulaForall::EqualTo(const FormulaCell &f) const {
  // Formula::EqualTo guarantees the following assertion.
  assert(get_kind() == f.get_kind());
  const FormulaForall &f_forall{static_cast<const FormulaForall &>(f)};
  return vars_ == f_forall.vars_ && f_.EqualTo(f_forall.f_);
}

bool FormulaForall::Less(const FormulaCell &f) const {
  // Formula::Less guarantees the following assertion.
  assert(get_kind() == f.get_kind());
  const FormulaForall &forall_f{static_cast<const FormulaForall &>(f)};
  if (vars_ < forall_f.vars_) {
    return true;
  }
  if (forall_f.vars_ < vars_) {
    return false;
  }
  return this->f_.Less(forall_f.f_);
}

bool FormulaForall::Evaluate(const Environment &) const {
  // Given ∀ x1, ..., xn. F, check if there is a counterexample satisfying
  // ¬F. If exists, it returns false. Otherwise, return true.
  // That is, it returns !check(∃ x1, ..., xn. ¬F)

  throw runtime_error("not implemented yet");
}

Formula FormulaForall::Substitute(const ExpressionSubstitution &expr_subst,
                                  const FormulaSubstitution &formula_subst) {
  // Quantified variables are already bound and should not be substituted by s.
  // We construct a new substitution new_s from s by removing the entries of
  // bound variables.
  ExpressionSubstitution new_expr_subst{expr_subst};
  FormulaSubstitution new_formula_subst{formula_subst};
  for (const Variable &var : vars_) {
    if (var.get_type() == Variable::Type::BOOLEAN) {
      new_formula_subst.erase(var);
    } else {
      new_expr_subst.erase(var);
    }
  }
  const Formula f_subst{f_.Substitute(new_expr_subst, new_formula_subst)};
  if (!f_.EqualTo(f_subst)) {
    return forall(vars_, f_subst);
  } else {
    return GetFormula();
  }
}

ostream &FormulaForall::Display(ostream &os) const {
  return os << "forall(" << vars_ << ". " << f_ << ")";
}
std::string FormulaForall::to_smt2_string() const {
  ostringstream oss;
  oss << "(forall(";
  for (const Variable &var : vars_) {
    oss << " " << var.get_name();
  }
  oss << ") " << f_.to_smt2_string() << ")";
  return oss.str();
}

bool is_false(const FormulaCell &f) {
  return f.get_kind() == FormulaKind::False;
}

bool is_true(const FormulaCell &f) { return f.get_kind() == FormulaKind::True; }

bool is_variable(const FormulaCell &f) {
  return f.get_kind() == FormulaKind::Var;
}

bool is_equal_to(const FormulaCell &f) {
  return f.get_kind() == FormulaKind::Eq;
}

bool is_not_equal_to(const FormulaCell &f) {
  return f.get_kind() == FormulaKind::Neq;
}

bool is_greater_than(const FormulaCell &f) {
  return f.get_kind() == FormulaKind::Gt;
}

bool is_greater_than_or_equal_to(const FormulaCell &f) {
  return f.get_kind() == FormulaKind::Geq;
}

bool is_less_than(const FormulaCell &f) {
  return f.get_kind() == FormulaKind::Lt;
}

bool is_less_than_or_equal_to(const FormulaCell &f) {
  return f.get_kind() == FormulaKind::Leq;
}

bool is_relational(const FormulaCell &f) {
  return is_equal_to(f) || is_not_equal_to(f) || is_greater_than(f) ||
      is_greater_than_or_equal_to(f) || is_less_than(f) ||
      is_less_than_or_equal_to(f);
}

bool is_conjunction(const FormulaCell &f) {
  return f.get_kind() == FormulaKind::And;
}

bool is_disjunction(const FormulaCell &f) {
  return f.get_kind() == FormulaKind::Or;
}

bool is_nary(const FormulaCell &f) {
  return is_conjunction(f) || is_disjunction(f);
}

bool is_negation(const FormulaCell &f) {
  return f.get_kind() == FormulaKind::Not;
}

bool is_forall(const FormulaCell &f) {
  return f.get_kind() == FormulaKind::Forall;
}

const FormulaFalse *to_false(const FormulaCell *f_ptr) {
  assert(is_false(*f_ptr));
  return static_cast<const FormulaFalse *>(f_ptr);
}

const FormulaFalse *to_false(const Formula &f) { return to_false(f.ptr_); }

const FormulaTrue *to_true(const FormulaCell *f_ptr) {
  assert(is_true(*f_ptr));
  return static_cast<const FormulaTrue *>(f_ptr);
}

const FormulaTrue *to_true(const Formula &f) { return to_true(f.ptr_); }

const FormulaVar *to_variable(const FormulaCell *f_ptr) {
  assert(is_variable(*f_ptr));
  return static_cast<const FormulaVar *>(f_ptr);
}

const FormulaVar *to_variable(const Formula &f) { return to_variable(f.ptr_); }

const RelationalFormulaCell *to_relational(const FormulaCell *f_ptr) {
  assert(is_relational(*f_ptr));
  return static_cast<const RelationalFormulaCell *>(f_ptr);
}

const RelationalFormulaCell *to_relational(const Formula &f) {
  return to_relational(f.ptr_);
}

const FormulaEq *to_equal_to(const FormulaCell *f_ptr) {
  assert(is_equal_to(*f_ptr));
  return static_cast<const FormulaEq *>(f_ptr);
}

const FormulaEq *to_equal_to(const Formula &f) { return to_equal_to(f.ptr_); }

const FormulaNeq *to_not_equal_to(const FormulaCell *f_ptr) {
  assert(is_not_equal_to(*f_ptr));
  return static_cast<const FormulaNeq *>(f_ptr);
}

const FormulaNeq *to_not_equal_to(const Formula &f) {
  return to_not_equal_to(f.ptr_);
}

const FormulaGt *to_greater_than(const FormulaCell *f_ptr) {
  assert(is_greater_than(*f_ptr));
  return static_cast<const FormulaGt *>(f_ptr);
}

const FormulaGt *to_greater_than(const Formula &f) {
  return to_greater_than(f.ptr_);
}

const FormulaGeq *to_greater_than_or_equal_to(const FormulaCell *f_ptr) {
  assert(is_greater_than_or_equal_to(*f_ptr));
  return static_cast<const FormulaGeq *>(f_ptr);
}

const FormulaGeq *to_greater_than_or_equal_to(const Formula &f) {
  return to_greater_than_or_equal_to(f.ptr_);
}

const FormulaLt *to_less_than(const FormulaCell *f_ptr) {
  assert(is_less_than(*f_ptr));
  return static_cast<const FormulaLt *>(f_ptr);
}

const FormulaLt *to_less_than(const Formula &f) { return to_less_than(f.ptr_); }

const FormulaLeq *to_less_than_or_equal_to(const FormulaCell *f_ptr) {
  assert(is_less_than_or_equal_to(*f_ptr));
  return static_cast<const FormulaLeq *>(f_ptr);
}

const FormulaLeq *to_less_than_or_equal_to(const Formula &f) {
  return to_less_than_or_equal_to(f.ptr_);
}

const NaryFormulaCell *to_nary(const FormulaCell *f_ptr) {
  assert(is_nary(*f_ptr));
  return static_cast<const NaryFormulaCell *>(f_ptr);
}

const NaryFormulaCell *to_nary(const Formula &f) { return to_nary(f.ptr_); }

NaryFormulaCell *to_nary(FormulaCell *f_ptr) {
  assert(is_nary(*f_ptr));
  return static_cast<NaryFormulaCell *>(f_ptr);
}

NaryFormulaCell *to_nary(Formula &f) { return to_nary(f.ptr_); }

const FormulaAnd *to_conjunction(const FormulaCell *f_ptr) {
  assert(is_conjunction(*f_ptr));
  return static_cast<const FormulaAnd *>(f_ptr);
}

const FormulaAnd *to_conjunction(const Formula &f) {
  return to_conjunction(f.ptr_);
}

const FormulaOr *to_disjunction(const FormulaCell *f_ptr) {
  assert(is_disjunction(*f_ptr));
  return static_cast<const FormulaOr *>(f_ptr);
}

const FormulaOr *to_disjunction(const Formula &f) {
  return to_disjunction(f.ptr_);
}

const FormulaNot *to_negation(const FormulaCell *f_ptr) {
  assert(is_negation(*f_ptr));
  return static_cast<const FormulaNot *>(f_ptr);
}

const FormulaNot *to_negation(const Formula &f) { return to_negation(f.ptr_); }

const FormulaForall *to_forall(const FormulaCell *f_ptr) {
  assert(is_forall(*f_ptr));
  return static_cast<const FormulaForall *>(f_ptr);
}

const FormulaForall *to_forall(const Formula &f) { return to_forall(f.ptr_); }

} // namespace dlinear::drake::symbolic


