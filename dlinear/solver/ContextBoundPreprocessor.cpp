/**
 * @file ContextBoundPreprocessor.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "ContextBoundPreprocessor.h"

#include <algorithm>
#include <cstddef>
#include <iterator>
#include <list>
#include <ostream>

#include "dlinear/libs/libgmp.h"
#include "dlinear/util/Infinity.h"
#include "dlinear/util/exception.h"

#if DEBUGGING_PREPROCESSOR
#include <string>

#include "dlinear/solver/Context.h"
#endif

namespace dlinear {

namespace {
#if 0
void cartesian_product(const std::set<LiteralSet>& a, const std::set<LiteralSet>& b, const std::set<LiteralSet>& c,
                       const LiteralSet& explanation_to_add, std::set<LiteralSet>& destination) {
  const std::set<LiteralSet> empty_set{{}};
  const std::set<LiteralSet>& first = a.empty() ? empty_set : a;
  const std::set<LiteralSet>& second = b.empty() ? empty_set : b;
  const std::set<LiteralSet>& third = c.empty() ? empty_set : c;
  for (const auto& a_set : first) {
    for (const auto& b_set : second) {
      for (const auto& c_set : third) {
        LiteralSet new_set;
        new_set.insert(a_set.begin(), a_set.end());
        new_set.insert(b_set.begin(), b_set.end());
        new_set.insert(c_set.begin(), c_set.end());
        new_set.insert(explanation_to_add.begin(), explanation_to_add.end());
        destination.insert(new_set);
      }
    }
  }
}
#endif

#if DEBUGGING_PREPROCESSOR

bool print_all = false;
Variable find_variable(const ContextBoundPreprocessor& preprocessor, const std::string& name) {
  for (const Variable& var : preprocessor.theory_cols())
    if (var.get_name() == name) return var;
  DLINEAR_UNREACHABLE();
}
bool check_explanation(const ContextBoundPreprocessor& preprocessor, const LiteralSet& explanation) {
  mpq_class zero{0};
  Config config = preprocessor.config();

  config.m_filename() = "";
  config.m_read_from_stdin() = false;
  config.m_disable_theory_preprocessor() = true;
  Context smt_solver{config};
  for (const auto& [var, truth] : explanation) {
    const Formula f = truth ? preprocessor.predicate_abstractor()[var] : !preprocessor.predicate_abstractor()[var];
    for (const Variable& free : f.GetFreeVariables()) {
      smt_solver.DeclareVariable(free);
    }
    smt_solver.Assert(f);
  }
  const auto result = smt_solver.CheckSat(&zero);
  if (result != SatResult::SAT_UNSATISFIABLE) {
    //    DLINEAR_RUNTIME_ERROR_FMT("The explanation {} is not valid", explanation);
    print_all = true;
    return false;
  }
  return true;
}
[[maybe_unused]] bool check_explanation(const ContextBoundPreprocessor& preprocessor,
                                        const std::set<LiteralSet>& explanations) {
  for (const auto& explanation : explanations) {
    return check_explanation(preprocessor, explanation);
  }
  return true;
}
#endif
}  // namespace

ContextBoundPreprocessor::ContextBoundPreprocessor(const PredicateAbstractor& predicate_abstractor)
    : config_{predicate_abstractor.config()}, predicate_abstractor_{predicate_abstractor} {}

ContextBoundVector::BoundIterator ContextBoundPreprocessor::AddConstraint(const Literal& lit) {
  const auto& [formula_var, truth] = lit;
  const Formula& formula = predicate_abstractor_[formula_var];

  // If the formula is a simple bound (e.g. x <= 1), immediately add it to the theory_bounds
  if (IsSimpleBound(formula)) {
    // We know there is exactly 1 variable in the formula
    const Variable& var = *formula.GetFreeVariables().cbegin();
    // Add the simple bound to the theory_bound. If a violation is detected, report it immediately
    const ContextBoundVector::BoundIterator violation{GetBoundVector(var).AddBound(GetBound(lit, formula))};
    if (!violation.empty()) return violation;
  };

  if (config_.disable_theory_preprocessor()) return {};
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::AddConstraint({}, {})", formula_var, formula);
  if (!ShouldPropagateEqBinomial(formula)) return {};
  const mpq_class coeff = ExtractEqBoundCoefficient(formula);
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::AddConstraint: {}, coeff = {}", formula, coeff);
  var_to_eq_binomial_edge_coefficients_.emplace(formula_var, coeff);
  return {};
}

void ContextBoundPreprocessor::GetActiveExplanation(const Variable& var, LiteralSet& explanation) {
  const auto it = theory_bounds_.find(var);
  if (it == theory_bounds_.end()) return;
  it->second.GetActiveExplanation(explanation);
}
ContextBoundPreprocessor::Explanations ContextBoundPreprocessor::Process(const LiteralSet& enabled_literals) {
  Explanations explanations;
  Process(enabled_literals, explanations);
  return explanations;
}
void ContextBoundPreprocessor::Process(const LiteralSet& enabled_literals, Explanations& explanations) {
  if (config_.disable_theory_preprocessor()) return;
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::Process({})", enabled_literals);
  std::list<Literal> mutable_enabled_formula_vars{enabled_literals.cbegin(), enabled_literals.cend()};
  SetEnvironmentFromBounds();

  // Remove all rows that have only one free variable, since they can't be propagated
  mutable_enabled_formula_vars.remove_if(
      [this](const Literal& lit) { return predicate_abstractor_[lit.var].GetFreeVariables().size() <= 1; });

  PropagateConstraints(mutable_enabled_formula_vars, explanations);
  DLINEAR_DEBUG_FMT("ContextBoundPreprocessor::Process: {} conflict found in propagation", explanations.size());
  if (!explanations.empty()) return;

  // Add back all rows that have only one free variable and were not active equality bounds before propagation
  //  for (const Literal& lit : enabled_literals) {
  //    const Formula& formula = predicate_abstractor_[lit.var];
  //    if (formula.GetFreeVariables().size() != 1) continue;
  //    if (theory_bounds_.at(*formula.GetFreeVariables().begin()).GetActiveEqualityBound() == nullptr) {
  //      mutable_enabled_formula_vars.push_back(lit);
  //    }
  //  }

  EvaluateFormulas(mutable_enabled_formula_vars, explanations);
  DLINEAR_DEBUG_FMT("ContextBoundPreprocessor::Process: {} conflict found in evaluation", explanations.size());
}

void ContextBoundPreprocessor::Clear() {
  env_ = Environment{};
  theory_bounds_.clear();
  temporary_mpq_vector_.clear();
}
void ContextBoundPreprocessor::Reset() {
  theory_bounds_ = fixed_theory_bounds_;
  env_ = fixed_env_;
  temporary_mpq_vector_ = fixed_temporary_mpq_vector_;
}

void ContextBoundPreprocessor::SetEnvironmentFromBounds() {
  for (const auto& [formula_var, bound] : theory_bounds_) {
    const mpq_class* const active_bound = bound.GetActiveEqualityBound();
    if (active_bound == nullptr) continue;
    env_[formula_var] = *active_bound;
    DLINEAR_TRACE_FMT("ContextBoundPreprocessor::SetEnvironmentFromBounds: {} = {}", formula_var, *active_bound);
  }
}

ContextBoundPreprocessor::PropagateResult ContextBoundPreprocessor::PropagateEqBinomial(const Literal& lit,
                                                                                        Explanations& explanations) {
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::PropagateEqBinomial({})", lit);

  const mpq_class& coeff = var_to_eq_binomial_edge_coefficients_.at(lit.var);
  const Formula& formula = predicate_abstractor_[lit.var];
  const auto& [from, to] = ExtractBoundEdge(formula);

  DLINEAR_ASSERT(is_equal_to(formula) || is_not_equal_to(formula), "Formula should be an = or != relation");
  DLINEAR_ASSERT(is_equal_to(formula) || !lit.truth, "If lit is true, formula must be an equality relation");
  DLINEAR_ASSERT(is_not_equal_to(formula) || lit.truth, "If lit is false, formula must be a not equal to relation");
  DLINEAR_ASSERT(formula.GetFreeVariables().size() == 2, "Formula should have exactly two free variables");
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");

  const Expression& lhs = get_lhs_expression(formula);
  const std::map<Expression, mpq_class>& map = get_expr_to_coeff_map_in_addition(lhs);
  DLINEAR_ASSERT(map.size() == 2, "Expression should have exactly two variables");
  DLINEAR_ASSERT(get_constant_value(get_rhs_expression(formula)) == 0, "The right-hand side must be 0");
  const bool from_is_first = get_variable(map.cbegin()->first).equal_to(from);

  Environment::const_iterator updater_it;
  Variable updating_variable;
  Variable to_update_variable;
  mpq_class new_value;
  if ((updater_it = env_.find(from)) != env_.end()) {
    DLINEAR_TRACE_FMT("ContextBoundPreprocessor::PropagateEqBinomial: {} -- {} --> {}", to, lit, from);
    new_value = from_is_first ? mpq_class{updater_it->second / coeff} : mpq_class{updater_it->second * coeff};
    updating_variable = from;
    to_update_variable = to;
  } else if ((updater_it = env_.find(to)) != env_.end()) {
    DLINEAR_TRACE_FMT("ContextBoundPreprocessor::PropagateEqBinomial: {} -- {} --> {}", from, lit, to);
    new_value = from_is_first ? mpq_class{updater_it->second * coeff} : mpq_class{updater_it->second / coeff};
    updating_variable = to;
    to_update_variable = from;
  } else {
    // Neither of the two variables is in the environment. Can't propagate
    return PropagateResult::NO_PROPAGATION;
  }

  auto to_update_it = env_.find(to_update_variable);

  fmt::println("ContextBoundPreprocessor::PropagateEqBinomial: {} -- {} --> {}", updating_variable, lit,
               to_update_variable);
  fmt::println("ContextBoundPreprocessor::PropagateEqBinomial: {} = {}", env_, theory_bounds_);

  // The value is the same as the one already in the environment. Nothing to propagate
  if (to_update_it != env_.end() && to_update_it->second == new_value) {
    return PropagateResult::UNCHANGED;
  }

  LiteralSet explanation = GetBoundVector(updating_variable).GetActiveEqExplanation();
  explanation.insert(lit);

  // The value was still not in the environment. Propagate it
  if (to_update_it == env_.end()) {
    const auto [it, inserted] = env_.insert(to_update_variable, new_value);
    DLINEAR_ASSERT(inserted, "The variable was not in the environment before");
    ContextBoundVector::BoundIterator violation =
        GetBoundVector(to_update_variable).AddBound(it->second, LpColBound::B, explanation);
    // Adding the new value to the environment caused a conflict in the bounds
    if (!violation.empty()) {
      for (; violation; ++violation) explanation.insert(violation->explanation.begin(), violation->explanation.end());
      DLINEAR_DEBUG_FMT("ContextBoundPreprocessor::PropagateEqBinomial: {} conflict found", explanation);
      explanations.insert(explanation);
      return PropagateResult::CONFLICT;
    }
    return PropagateResult::PROPAGATED;
  }

  // The value conflicts with the one already in the environment
  DLINEAR_ASSERT(to_update_it->second != new_value, "A conflict must have been detected");
  const LiteralSet to_update_explanation = GetBoundVector(to_update_variable).GetActiveEqExplanation();
  explanation.insert(to_update_explanation.begin(), to_update_explanation.end());
  explanations.insert(explanation);
  return PropagateResult::CONFLICT;
}

ContextBoundPreprocessor::PropagateResult ContextBoundPreprocessor::PropagateEqPolynomial(const Literal& lit,
                                                                                          Explanations& explanations) {
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::PropagateEqPolynomial({})", lit);

  const Formula& formula = predicate_abstractor_[lit.var];

  DLINEAR_ASSERT(is_equal_to(formula) || is_not_equal_to(formula), "Formula should be an = or != relation");
  DLINEAR_ASSERT(is_equal_to(formula) || !lit.truth, "If lit is true, formula must be an equality relation");
  DLINEAR_ASSERT(is_not_equal_to(formula) || lit.truth, "If lit is false, formula must be a not equal to relation");
  DLINEAR_ASSERT(formula.GetFreeVariables().size() > 2, "Formula should have more than two free variables");
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  DLINEAR_ASSERT(ShouldPropagateEqPolynomial(lit), "The formula should be propagated");

  LiteralSet explanation{lit};
  std::vector<Variable> dependencies;
  mpq_class rhs{get_constant_value(get_rhs_expression(formula))};
  mpq_class var_coeff{};
  Variable var_propagated{};
  for (const auto& [expr, coeff] : get_expr_to_coeff_map_in_addition(get_lhs_expression(formula))) {
    DLINEAR_ASSERT(is_variable(expr), "All expressions in lhs formula must be variables");
    const Variable& var = get_variable(expr);
    const auto env_it = env_.find(var);
    if (env_it != env_.cend()) {
      rhs -= env_it->second * coeff;
      dependencies.emplace_back(var);
    } else {
      var_propagated = var;
      var_coeff = coeff;
    }
  }
  DLINEAR_ASSERT(!var_propagated.is_dummy(), "There must be exactly a propagated variable");
  DLINEAR_ASSERT(var_coeff != 0, "The propagated variable coefficient cannot be 0");

  // Calculate the propagated value of the variable
  rhs /= var_coeff;
  // Add all the dependencies edges to the graph
  for (const Variable& dependency : dependencies) {
    const LiteralSet dependency_explanation = GetBoundVector(dependency).GetActiveEqExplanation();
    explanation.insert(dependency_explanation.begin(), dependency_explanation.end());
  }
  const auto [env_it, inserted] = env_.insert(var_propagated, rhs);
  DLINEAR_ASSERT(inserted, "The variable was not in the environment before");
  fmt::println("ContextBoundPreprocessor::PropagateConstraints: {} = {} thanks to constraint {} and {}", var_propagated,
               rhs, lit, dependencies);
  ContextBoundVector::BoundIterator violation{
      GetBoundVector(var_propagated).AddBound(env_it->second, LpColBound::B, explanation)};
  if (!violation.empty()) {
    for (; violation; ++violation) explanation.insert(violation->explanation.begin(), violation->explanation.end());
    DLINEAR_DEBUG_FMT("ContextBoundPreprocessor::PropagateConstraints: {} conflict found", explanation);
    explanations.insert(explanation);
    // Remove the propagated constraint from the environment
    env_.erase(env_it);
    return PropagateResult::CONFLICT;
  }
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::PropagateConstraints: {} = {} thanks to constraint {} and {}",
                    var_propagated, rhs, lit, dependencies);
  return PropagateResult::PROPAGATED;
}

ContextBoundPreprocessor::PropagateResult ContextBoundPreprocessor::PropagateInBinomial(const Literal& lit,
                                                                                        Explanations& explanations) {
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::PropagateEqBinomial({})", lit);

  const Formula& formula = predicate_abstractor_[lit.var];
  LiteralSet explanation{lit};

  DLINEAR_ASSERT(!is_equal_to(formula) && !is_not_equal_to(formula), "Formula should be an = or != relation");
  DLINEAR_ASSERT(formula.GetFreeVariables().size() == 2, "Formula should have exactly two free variables");
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");

  const Expression& lhs = get_lhs_expression(formula);
  const std::map<Expression, mpq_class>& map = get_expr_to_coeff_map_in_addition(lhs);
  DLINEAR_ASSERT(map.size() == 2, "Expression should have exactly two variables");
  DLINEAR_ASSERT(get_constant_value(get_rhs_expression(formula)) == 0, "The right-hand side must be 0");

  mpq_class l_rhs{get_constant_value(get_rhs_expression(formula))};
  mpq_class u_rhs{get_constant_value(get_rhs_expression(formula))};

  const Variable& first = get_variable(map.begin()->first);
  const Variable& second = get_variable(std::next(map.begin())->first);

  const Variable from = GetBoundVector(first).IsBounded() ? first : second;
  const Variable to = from.equal_to(first) ? second : first;
  DLINEAR_ASSERT(GetBoundVector(from).IsBounded(), "At least one variable must be bounded");
  DLINEAR_ASSERT(!GetBoundVector(to).IsBounded(), "At least one variable must be unbounded");
  const mpq_class& from_value = from.equal_to(first) ? map.begin()->second : std::next(map.begin())->second;
  const mpq_class& to_value = from.equal_to(first) ? std::next(map.begin())->second : map.begin()->second;

  // Cases:
  // 1. ax + by > c     =>  x in [l, u] => y in [(c - ua)/b, -]
  // 2. -ax + by > c    =>  x in [l, u] => y in [(c + la)/b, -]
  // 3. ax + -by > c    =>  x in [l, u] => y in [-, (-c + ua)/b]
  // 4. -ax + -by > c   =>  x in [l, u] => y in [-, (-c - la)/b]

  // 5. ax + by < c     =>  x in [l, u] => y in [-, (c - la)/b]
  // 6. -ax + by < c    =>  x in [l, u] => y in [-, (c + ua)/b]
  // 7. ax + -by < c    =>  x in [l, u] => y in [(-c + la)/b, -]
  // 8. -ax + -by < c   =>  x in [l, u] => y in [(-c - ua)/b, -]

  if (from_value > 0) {
    l_rhs -= GetBoundVector(from).active_upper_bound() * from_value;
    u_rhs -= GetBoundVector(from).active_lower_bound() * from_value;
  } else {
    l_rhs -= GetBoundVector(from).active_lower_bound() * from_value;
    u_rhs -= GetBoundVector(from).active_upper_bound() * from_value;
  }

  l_rhs /= to_value;
  u_rhs /= to_value;

  if ((lit.truth && is_equal_to(formula)) || (!lit.truth && is_not_equal_to(formula))) {
    ContextBoundVector::Bound bound{StoreTemporaryMpq(l_rhs), LpColBound::L, explanation};
    ContextBoundVector::BoundIterator violation{GetBoundVector(to).AddBound(bound)};
    if (!violation.empty()) {
      for (; violation; ++violation) explanation.insert(violation->explanation.begin(), violation->explanation.end());
      DLINEAR_DEBUG_FMT("ContextBoundPreprocessor::PropagateConstraints: {} conflict found", explanation);
      explanations.insert(explanation);
      return PropagateResult::CONFLICT;
    }
    ContextBoundVector::Bound bound2{StoreTemporaryMpq(u_rhs), LpColBound::U, explanation};
    ContextBoundVector::BoundIterator violation2{GetBoundVector(to).AddBound(bound2)};
    if (!violation2.empty()) {
      for (; violation2; ++violation2)
        explanation.insert(violation2->explanation.begin(), violation2->explanation.end());
      DLINEAR_DEBUG_FMT("ContextBoundPreprocessor::PropagateConstraints: {} conflict found", explanation);
      explanations.insert(explanation);
      return PropagateResult::CONFLICT;
    }
    return PropagateResult::PROPAGATED;
  }

  ContextBoundVector::Bound bound;
  if (to_value > 0) {
    if (is_greater_than(formula)) {
      bound = {StoreTemporaryMpq(l_rhs), LpColBound::SL, explanation};
    } else if (is_greater_than_or_equal_to(formula)) {
      bound = {StoreTemporaryMpq(l_rhs), LpColBound::L, explanation};
    } else if (is_less_than(formula)) {
      bound = {StoreTemporaryMpq(u_rhs), LpColBound::SU, explanation};
    } else {
      DLINEAR_ASSERT(is_less_than_or_equal_to(formula), "The formula must be a less than or equal to relation");
      bound = {StoreTemporaryMpq(u_rhs), LpColBound::U, explanation};
    }
  } else {
    if (is_greater_than(formula)) {
      bound = {StoreTemporaryMpq(u_rhs), LpColBound::SU, explanation};
    } else if (is_greater_than_or_equal_to(formula)) {
      bound = {StoreTemporaryMpq(u_rhs), LpColBound::U, explanation};
    } else if (is_less_than(formula)) {
      bound = {StoreTemporaryMpq(l_rhs), LpColBound::SL, explanation};
    } else {
      DLINEAR_ASSERT(is_less_than_or_equal_to(formula), "The formula must be a less than or equal to relation");
      bound = {StoreTemporaryMpq(l_rhs), LpColBound::L, explanation};
    }
  }

  ContextBoundVector::BoundIterator violation{GetBoundVector(to).AddBound(bound)};
  if (!violation.empty()) {
    for (; violation; ++violation) explanation.insert(violation->explanation.begin(), violation->explanation.end());
    DLINEAR_DEBUG_FMT("ContextBoundPreprocessor::PropagateInBinomial: {} conflict found", explanation);
    explanations.insert(explanation);
    return PropagateResult::CONFLICT;
  }

  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::PropagateConstraints: {} = [{}, {}] thanks to constraint {}", to, l_rhs,
                    u_rhs, lit);
  return PropagateResult::PROPAGATED;
}

ContextBoundPreprocessor::PropagateResult ContextBoundPreprocessor::PropagateInPolynomial(const Literal& lit,
                                                                                          Explanations& explanations) {
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::PropagateInPolynomial({})", lit);

  const Formula& formula = predicate_abstractor_[lit.var];

  DLINEAR_ASSERT(is_relational(formula), "Formula should be a relational relation other than = or !=");
  DLINEAR_ASSERT(formula.GetFreeVariables().size() > 2, "Formula should have more than two free variables");
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  DLINEAR_ASSERT(ShouldPropagateInPolynomial(lit), "The formula should be propagated");

  LiteralSet explanation{lit};
  std::vector<Variable> dependencies;
  mpq_class l_rhs{get_constant_value(get_rhs_expression(formula))};
  mpq_class u_rhs{get_constant_value(get_rhs_expression(formula))};
  mpq_class var_coeff{};
  Variable var_propagated{};
  for (const auto& [expr, coeff] : get_expr_to_coeff_map_in_addition(get_lhs_expression(formula))) {
    DLINEAR_ASSERT(is_variable(expr), "All expressions in lhs formula must be variables");
    const Variable& var = get_variable(expr);
    if (GetBoundVector(var).IsBounded()) {
      if (coeff > 0) {
        l_rhs -= GetBoundVector(var).active_upper_bound() * coeff;
        u_rhs -= GetBoundVector(var).active_lower_bound() * coeff;
      } else {
        l_rhs -= GetBoundVector(var).active_lower_bound() * coeff;
        u_rhs -= GetBoundVector(var).active_upper_bound() * coeff;
      }
    } else {
      var_propagated = var;
      var_coeff = coeff;
    }
  }
  DLINEAR_ASSERT(!var_propagated.is_dummy(), "There must be exactly a propagated variable");
  DLINEAR_ASSERT(var_coeff != 0, "The propagated variable coefficient cannot be 0");

  // Calculate the propagated value of the bounds
  l_rhs /= var_coeff;
  u_rhs /= var_coeff;

  // Add all the dependencies edges to the explanation
  for (const Variable& dependency : dependencies) {
    const LiteralSet dependency_explanation = GetBoundVector(dependency).GetActiveEqExplanation();
    explanation.insert(dependency_explanation.begin(), dependency_explanation.end());
  }

  if ((lit.truth && is_equal_to(formula)) || (!lit.truth && is_not_equal_to(formula))) {
    ContextBoundVector::Bound bound{StoreTemporaryMpq(l_rhs), LpColBound::L, explanation};
    ContextBoundVector::BoundIterator violation{GetBoundVector(var_propagated).AddBound(bound)};
    if (!violation.empty()) {
      for (; violation; ++violation) explanation.insert(violation->explanation.begin(), violation->explanation.end());
      DLINEAR_DEBUG_FMT("ContextBoundPreprocessor::PropagateConstraints: {} conflict found", explanation);
      explanations.insert(explanation);
      return PropagateResult::CONFLICT;
    }
    ContextBoundVector::Bound bound2{StoreTemporaryMpq(u_rhs), LpColBound::U, explanation};
    ContextBoundVector::BoundIterator violation2{GetBoundVector(var_propagated).AddBound(bound2)};
    if (!violation2.empty()) {
      for (; violation2; ++violation2)
        explanation.insert(violation2->explanation.begin(), violation2->explanation.end());
      DLINEAR_DEBUG_FMT("ContextBoundPreprocessor::PropagateConstraints: {} conflict found", explanation);
      explanations.insert(explanation);
      return PropagateResult::CONFLICT;
    }
    return PropagateResult::PROPAGATED;
  }

  ContextBoundVector::Bound bound;
  // Add the bound on the single unbounded variable based on the upper and lower bound computed over the polynomial
  if (var_coeff > 0) {
    if (is_greater_than(formula)) {
      bound = {StoreTemporaryMpq(l_rhs), LpColBound::SL, explanation};
    } else if (is_greater_than_or_equal_to(formula)) {
      bound = {StoreTemporaryMpq(l_rhs), LpColBound::L, explanation};
    } else if (is_less_than(formula)) {
      bound = {StoreTemporaryMpq(u_rhs), LpColBound::SU, explanation};
    } else {
      DLINEAR_ASSERT(is_less_than_or_equal_to(formula), "The formula must be a less than or equal to relation");
      bound = {StoreTemporaryMpq(u_rhs), LpColBound::U, explanation};
    }
  } else {
    DLINEAR_ASSERT(var_coeff < 0, "The coefficient must be less than 0");
    if (is_greater_than(formula)) {
      bound = {StoreTemporaryMpq(u_rhs), LpColBound::SU, explanation};
    } else if (is_greater_than_or_equal_to(formula)) {
      bound = {StoreTemporaryMpq(u_rhs), LpColBound::U, explanation};
    } else if (is_less_than(formula)) {
      bound = {StoreTemporaryMpq(l_rhs), LpColBound::SL, explanation};
    } else {
      DLINEAR_ASSERT(is_less_than_or_equal_to(formula), "The formula must be a less than or equal to relation");
      bound = {StoreTemporaryMpq(l_rhs), LpColBound::L, explanation};
    }
  }
  fmt::println("ContextBoundPreprocessor::PropagateConstraints: {} = [{}, {}] thanks to constraint {} and {}",
               var_propagated, l_rhs, u_rhs, lit, dependencies);
  ContextBoundVector::BoundIterator violation{GetBoundVector(var_propagated).AddBound(bound)};
  if (!violation.empty()) {
    for (; violation; ++violation) explanation.insert(violation->explanation.begin(), violation->explanation.end());
    DLINEAR_DEBUG_FMT("ContextBoundPreprocessor::PropagateConstraints: {} conflict found", explanation);
    explanations.insert(explanation);
    return PropagateResult::CONFLICT;
  }
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::PropagateConstraints: {} = [{}, {}] thanks to constraint {} and {}",
                    var_propagated, l_rhs, u_rhs, lit, dependencies);
  return PropagateResult::PROPAGATED;
}

void ContextBoundPreprocessor::PropagateConstraints(std::list<Literal>& enabled_literals, Explanations& explanations) {
  DLINEAR_TRACE("ContextBoundPreprocessor::PropagateConstraints()");
  fmt::println("ContextBoundPreprocessor::PropagateConstraints({})", enabled_literals);
  bool continue_propagating;
  // While we still have constraints to propagate...
  do {
    continue_propagating = false;
    for (auto it = enabled_literals.begin(); it != enabled_literals.end();) {
      const Literal& lit = *it;
      fmt::println("ContextBoundPreprocessor: propagating {}", lit);
      // Simple binomial equality. Handle it more efficiently
      if (ShouldPropagateEqBinomial(lit)) {
        const PropagateResult propagation_result = PropagateEqBinomial(lit, explanations);
        switch (propagation_result) {
          case PropagateResult::NO_PROPAGATION:
            ++it;
            continue;
          case PropagateResult::PROPAGATED:
            continue_propagating = true;
            [[fallthrough]];
          case PropagateResult::UNCHANGED:
          case PropagateResult::CONFLICT:
            it = enabled_literals.erase(it);
            continue;
        }
      }
      // Equality polynomial missing a single variable. Propagate it
      if (ShouldPropagateEqPolynomial(lit)) {
        const PropagateResult propagation_result = PropagateEqPolynomial(lit, explanations);
        if (propagation_result == PropagateResult::PROPAGATED) {
          continue_propagating = true;
          it = enabled_literals.erase(it);
        } else {
          DLINEAR_ASSERT(propagation_result == PropagateResult::CONFLICT, "The propagation result must be a conflict");
          ++it;
        }
        continue;
      }
      ++it;
    }
  } while (continue_propagating && explanations.empty());
  do {
    continue_propagating = false;
    for (auto it = enabled_literals.begin(); it != enabled_literals.end();) {
      const Literal& lit = *it;
      fmt::println("ContextBoundPreprocessor: propagating {} - {} - {}\n{}", lit, ShouldPropagateInBinomial(lit),
                   ShouldPropagateInPolynomial(lit), theory_bounds_);
      std::cout << std::endl;
      if (ShouldPropagateInBinomial(lit)) {
        const PropagateResult propagation_result = PropagateInBinomial(lit, explanations);
        if (propagation_result == PropagateResult::PROPAGATED) {
          continue_propagating = true;
          it = enabled_literals.erase(it);
        } else {
          DLINEAR_ASSERT(propagation_result == PropagateResult::CONFLICT, "The propagation result must be a conflict");
          ++it;
        }
        continue;
      }
      if (ShouldPropagateInPolynomial(lit)) {
        const PropagateResult propagation_result = PropagateInPolynomial(lit, explanations);
        if (propagation_result == PropagateResult::PROPAGATED) {
          continue_propagating = true;
          it = enabled_literals.erase(it);
        } else {
          DLINEAR_ASSERT(propagation_result == PropagateResult::CONFLICT, "The propagation result must be a conflict");
          ++it;
        }
        continue;
      }
      ++it;
    }
  } while (continue_propagating && explanations.empty());
}

void ContextBoundPreprocessor::EvaluateFormulas(std::list<Literal>& enabled_literals, Explanations& explanations) {
  DLINEAR_ASSERT(explanations.empty(), "The explanations vector must be empty");
  DLINEAR_TRACE("ContextBoundPreprocessor::EvaluateFormulas()");
  for (const Literal& lit : enabled_literals) {
    if (!ShouldEvaluate(lit)) continue;
    const Formula& formula = predicate_abstractor_[lit.var];
    const bool satisfied = formula.Evaluate(env_) == lit.truth;
    if (!satisfied) {
      DLINEAR_DEBUG_FMT("ContextBoundPreprocessor::EvaluateFormulas: {} => FAIL", lit);
      FormulaViolationExplanation(lit, formula, explanations);
    }
  }
}

void ContextBoundPreprocessor::FormulaViolationExplanation(const Literal& lit, const Formula& formula,
                                                           Explanations& explanations) {
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::FormulaViolationExplanation({})", formula);
  // TODO: produce more than just one explanation! Produce as many as possible!
  LiteralSet explanation;
  explanation.insert(lit);
  for (const auto& var : formula.GetFreeVariables()) {
    DLINEAR_ASSERT(env_.find(var) != env_.end(), "All free variables must be in the environment");
    GetExplanation(var, explanation);
  }
#if DEBUGGING_PREPROCESSOR
  const bool res = check_explanation(*this, explanation);
  if (!res) {
    for (const auto& var : formula.GetFreeVariables()) {
      // fmt::println("Explanation origins: {} --> {}", var, GetExplanationOrigins(var));
      LiteralSet ex;
      GetExplanation(var, ex);
      // fmt::println("Explanation: {} --> {}", var, ex);
    }
    for (const auto& var_name : {"x_87", "x_97"}) {
      Variable var = find_variable(*this, var_name);
      // fmt::println("Explanation origins: {} --> {}", var, GetExplanationOrigins(var));
      LiteralSet ex;
      GetExplanation(var, ex);
      // fmt::println("Explanation: {} --> {}", var, ex);
    }
    DLINEAR_ASSERT(res, "Explanation must be valid");
  }
#endif
  explanations.insert(explanation);
}

bool ContextBoundPreprocessor::ShouldEvaluate(const Literal& lit) const {
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::ShouldEvaluate({})", lit);
  const Formula& formula = predicate_abstractor_[lit.var];
  return ShouldEvaluate(formula);
}
bool ContextBoundPreprocessor::ShouldEvaluate(const Formula& formula) const {
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::ShouldEvaluate({})", formula);
  // All free variables must be in the environment
  return std::all_of(formula.GetFreeVariables().begin(), formula.GetFreeVariables().end(),
                     [this](const Variable& v) { return env_.contains(v); });
}

bool ContextBoundPreprocessor::ShouldPropagateEqBinomial(const Literal& lit) const {
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::ShouldPropagateEqBinomial({})", lit);
  const auto& [formula_var, truth] = lit;
  const Formula& formula = predicate_abstractor_[formula_var];
  // There must be exactly two free variables and an equality relation between them
  if (truth && !is_equal_to(formula)) return false;
  if (!truth && !is_not_equal_to(formula)) return false;
  return ShouldPropagateEqBinomial(formula);
}
bool ContextBoundPreprocessor::ShouldPropagateEqBinomial(const Formula& formula) const {
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::ShouldPropagateEqBinomial({})", formula);
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  // There must be exactly two free variables and an equality relation between them
  if (formula.GetFreeVariables().size() != 2) return false;
  if (!is_equal_to(formula) && !is_not_equal_to(formula)) return false;

  // The formula must be of the form 'ax == by + c', with a,b != 0
  const Expression& lhs = get_lhs_expression(formula);
  if (!is_addition(lhs) || get_constant_in_addition(lhs) != 0) return false;
  const auto& expr_to_coeff_map = to_addition(lhs)->get_expr_to_coeff_map();
  if (expr_to_coeff_map.size() != 2) return false;
  return is_variable(expr_to_coeff_map.cbegin()->first) && is_variable(std::next(expr_to_coeff_map.cbegin())->first) &&
         expr_to_coeff_map.cbegin()->second != 0 && std::next(expr_to_coeff_map.cbegin())->second != 0;
}

bool ContextBoundPreprocessor::ShouldPropagateEqPolynomial(const Literal& lit) const {
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::ShouldPropagateEqPolynomial({})", lit);
  const auto& [formula_var, truth] = lit;
  const Formula& formula = predicate_abstractor_[formula_var];
  // There must be exactly two free variables and an equality relation between them
  if (truth && !is_equal_to(formula)) return false;
  if (!truth && !is_not_equal_to(formula)) return false;
  return ShouldPropagateEqPolynomial(formula);
}
bool ContextBoundPreprocessor::ShouldPropagateEqPolynomial(const Formula& formula) const {
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::ShouldPropagateEqPolynomial({})", formula);
  // There must be exactly two free variables and an equality relation between them
  if (!is_equal_to(formula) && !is_not_equal_to(formula)) return false;
  if (formula.GetFreeVariables().size() < 2) return false;
  DLINEAR_ASSERT(is_addition(get_lhs_expression(formula)), "lhs expression must be an addition");

  // The formula must be of the form 'a1x1 + a2x2 + ... + anxn + c = b', with ai,b != 0
  std::size_t missing_var_count{0};
  for (const auto& [expr, coeff] : get_expr_to_coeff_map_in_addition(get_lhs_expression(formula))) {
    DLINEAR_ASSERT(is_variable(expr), "All expressions in lhs formula must be variables");
    if (env_.find(get_variable(expr)) != env_.cend()) continue;
    if (++missing_var_count > 1) return false;
  }
  return missing_var_count == 1;
}
bool ContextBoundPreprocessor::ShouldPropagateInBinomial(const Literal& lit) const {
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::ShouldPropagateInBinomial({})", lit);
  const auto& [formula_var, truth] = lit;
  const Formula& formula = predicate_abstractor_[formula_var];
  // There must be exactly two free variables and an equality relation between them
  if (!is_relational(formula)) return false;
  return ShouldPropagateInBinomial(formula);
}
bool ContextBoundPreprocessor::ShouldPropagateInBinomial(const Formula& formula) const {
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::ShouldPropagateInBinomial({})", formula);
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  // There must be exactly two free variables and an equality relation between them
  if (!is_relational(formula)) return false;
  if (formula.GetFreeVariables().size() != 2) return false;

  // The formula must be of the form 'ax <=> by + c', with a,b != 0 and <=> in {<, <=, >, >=, !=}
  const Expression& lhs = get_lhs_expression(formula);
  if (!is_addition(lhs) || get_constant_in_addition(lhs) != 0) return false;
  const auto& expr_to_coeff_map = to_addition(lhs)->get_expr_to_coeff_map();
  if (expr_to_coeff_map.size() != 2) return false;

  const Variable& first = get_variable(expr_to_coeff_map.cbegin()->first);
  const Variable& second = get_variable(std::next(expr_to_coeff_map.cbegin())->first);
  if (expr_to_coeff_map.cbegin()->second == 0 || std::next(expr_to_coeff_map.cbegin())->second == 0) return false;
  const auto it = theory_bounds_.find(first);
  if (it == theory_bounds_.end() || !it->second.IsBounded())
    return theory_bounds_.find(second) != theory_bounds_.end() && theory_bounds_.at(second).IsBounded();
  return theory_bounds_.find(second) == theory_bounds_.end() && !theory_bounds_.at(second).IsBounded();
}
bool ContextBoundPreprocessor::ShouldPropagateInPolynomial(const Literal& lit) const {
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::ShouldPropagateInPolynomial({})", lit);
  const auto& [formula_var, truth] = lit;
  const Formula& formula = predicate_abstractor_[formula_var];
  // There must be exactly two free variables and an equality relation between them
  if (!is_relational(formula)) return false;
  return ShouldPropagateInPolynomial(formula);
}
bool ContextBoundPreprocessor::ShouldPropagateInPolynomial(const Formula& formula) const {
  DLINEAR_TRACE_FMT("ContextBoundPreprocessor::ShouldPropagateInPolynomial({})", formula);
  // There must be more than two free variables and an inequality relation between them
  if (!is_relational(formula)) return false;
  if (formula.GetFreeVariables().size() < 2) return false;
  DLINEAR_ASSERT(is_addition(get_lhs_expression(formula)), "lhs expression must be an addition");

  // TODO(tend): being naive, this approach will not propagate some bounds that could be propagated
  //  since it forces the dependency variables to be bounded both ways for propagation
  // The formula must be of the form 'a1x1 + a2x2 + ... + anxn + c <=> b', with ai,b != 0 and <=> in {<, <=, >, >=, !=}
  std::size_t missing_var_count{0};
  for (const auto& [expr, coeff] : get_expr_to_coeff_map_in_addition(get_lhs_expression(formula))) {
    DLINEAR_ASSERT(is_variable(expr), "All expressions in lhs formula must be variables");
    const Variable& var = get_variable(expr);
    const auto it = theory_bounds_.find(var);
    if (it == theory_bounds_.end() || !it->second.IsBounded()) {
      if (++missing_var_count > 1) return false;
      continue;
    }
  }
  return missing_var_count == 1;
}

std::pair<Variable, Variable> ContextBoundPreprocessor::ExtractBoundEdge(const Formula& formula) const {
  DLINEAR_ASSERT(formula.GetFreeVariables().size() == 2, "Formula should have exactly two free variables");
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  const Expression& lhs = get_lhs_expression(formula);

  const std::map<Expression, mpq_class>& map = get_expr_to_coeff_map_in_addition(lhs);
  DLINEAR_ASSERT(map.size() == 2, "Expression should have exactly two variables");
  DLINEAR_ASSERT(get_constant_value(get_rhs_expression(formula)) == 0, "The right-hand side must be 0");

  return {
      get_variable(map.cbegin()->first),             // From vertex (variable)
      get_variable(std::next(map.cbegin())->first),  // To vertex (variable)
  };
}

mpq_class ContextBoundPreprocessor::ExtractEqBoundCoefficient(const Formula& formula) const {
  DLINEAR_ASSERT(is_equal_to(formula), "Formula should be an equality relation");
  DLINEAR_ASSERT(formula.GetFreeVariables().size() == 2, "Formula should have exactly two free variables");
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  const Expression& lhs = get_lhs_expression(formula);

  const std::map<Expression, mpq_class>& map = get_expr_to_coeff_map_in_addition(lhs);
  DLINEAR_ASSERT(map.size() == 2, "Expression should have exactly two variables");
  DLINEAR_ASSERT(get_constant_value(get_rhs_expression(formula)) == 0, "The right-hand side must be 0");

  return -(std::next(map.cbegin())->second) / map.cbegin()->second;
}

const mpq_class* ContextBoundPreprocessor::StoreTemporaryMpq(const mpq_class& value) {
  temporary_mpq_vector_.emplace_back(value);
  return &temporary_mpq_vector_.back();
}

ContextBoundVector& ContextBoundPreprocessor::GetBoundVector(const Variable& var) {
  const auto [it, inserted] =
      theory_bounds_.emplace(var, ContextBoundVector{Infinity::ninfinity(config_), Infinity::infinity(config_)});
  return it->second;
}
ContextBoundVector::Bound ContextBoundPreprocessor::GetBound(const dlinear::Literal& lit) const {
  return GetBound(lit, predicate_abstractor_[lit.var]);
}
ContextBoundVector::Bound ContextBoundPreprocessor::GetBound(const Literal& lit, const Formula& formula) const {
  DLINEAR_ASSERT(IsSimpleBound(formula), "Formula must be a simple bound");
  const Expression& lhs{get_lhs_expression(formula)};
  const Expression& rhs{get_rhs_expression(formula)};
  if (IsEqualTo(formula, lit.truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {&get_constant_value(rhs), LpColBound::B, {lit}};
    if (is_constant(lhs) && is_variable(rhs)) return {&get_constant_value(lhs), LpColBound::B, {lit}};
  }
  if (IsGreaterThan(formula, lit.truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {&get_constant_value(rhs), LpColBound::SL, {lit}};
    if (is_constant(lhs) && is_variable(rhs)) return {&get_constant_value(lhs), LpColBound::SU, {lit}};
  }
  if (IsGreaterThanOrEqualTo(formula, lit.truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {&get_constant_value(rhs), LpColBound::L, {lit}};
    if (is_constant(lhs) && is_variable(rhs)) return {&get_constant_value(lhs), LpColBound::U, {lit}};
  }
  if (IsLessThan(formula, lit.truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {&get_constant_value(rhs), LpColBound::SU, {lit}};
    if (is_constant(lhs) && is_variable(rhs)) return {&get_constant_value(lhs), LpColBound::SL, {lit}};
  }
  if (IsLessThanOrEqualTo(formula, lit.truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {&get_constant_value(rhs), LpColBound::U, {lit}};
    if (is_constant(lhs) && is_variable(rhs)) return {&get_constant_value(lhs), LpColBound::L, {lit}};
  }
  if (IsNotEqualTo(formula, lit.truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {&get_constant_value(rhs), LpColBound::D, {lit}};
    if (is_constant(lhs) && is_variable(rhs)) return {&get_constant_value(lhs), LpColBound::D, {lit}};
  }
  DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
}

bool ContextBoundPreprocessor::IsSimpleBound(const Formula& formula) {
  // Formula must be a relational formula: `lhs <= rhs`, `lhs >= rhs`, `lhs == rhs` or `lhs != rhs`.
  if (!is_relational(formula)) return false;
  // The number of variables must be exactly one
  if (formula.GetFreeVariables().size() != 1) return false;

  // one between lhs and rhs must be a constant and the other must be a variable.
  const Expression& lhs{get_lhs_expression(formula)};
  const Expression& rhs{get_rhs_expression(formula)};
  return ((is_constant(lhs) && is_variable(rhs)) || (is_variable(lhs) && is_constant(rhs)));
}

bool ContextBoundPreprocessor::IsEqualTo(const Formula& formula, const bool truth) {
  return truth ? is_equal_to(formula) : is_not_equal_to(formula);
}

bool ContextBoundPreprocessor::IsNotEqualTo(const Formula& formula, const bool truth) {
  return truth ? is_not_equal_to(formula) : is_equal_to(formula);
}

bool ContextBoundPreprocessor::IsGreaterThan(const Formula& formula, const bool truth) {
  return truth ? is_greater_than(formula) : is_less_than_or_equal_to(formula);
}

bool ContextBoundPreprocessor::IsLessThan(const Formula& formula, const bool truth) {
  return truth ? is_less_than(formula) : is_greater_than_or_equal_to(formula);
}

bool ContextBoundPreprocessor::IsGreaterThanOrEqualTo(const Formula& formula, const bool truth) {
  return truth ? is_greater_than_or_equal_to(formula) : is_less_than(formula);
}

bool ContextBoundPreprocessor::IsLessThanOrEqualTo(const Formula& formula, const bool truth) {
  return truth ? is_less_than_or_equal_to(formula) : is_greater_than(formula);
}

void ContextBoundPreprocessor::GetExplanation(const Variable& var, LiteralSet& explanation) {
  const auto it = theory_bounds_.find(var);
  if (it == theory_bounds_.end()) return;
  it->second.GetActiveExplanation(explanation);
}

std::ostream& operator<<(std::ostream& os, const ContextBoundPreprocessor& preprocessor) {
  return os << "ContextBoundPreprocessor{" << "env_ = " << preprocessor.env() << ", "
            << "theory_bounds_ = " << preprocessor.theory_bounds() << "}";
}

}  // namespace dlinear
