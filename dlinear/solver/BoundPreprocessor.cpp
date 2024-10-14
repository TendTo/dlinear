/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "BoundPreprocessor.h"

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
Variable find_variable(const BoundPreprocessor& preprocessor, const std::string& name) {
  for (const Variable& var : preprocessor.theory_cols())
    if (var.get_name() == name) return var;
  DLINEAR_UNREACHABLE();
}
bool check_explanation(const BoundPreprocessor& preprocessor, const LiteralSet& explanation) {
  mpq_class zero{0};
  Config config = preprocessor.config();

  config.m_filename() = "";
  config.m_read_from_stdin() = false;
  config.m_disable_eq_propagation() = true;
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
[[maybe_unused]] bool check_explanation(const BoundPreprocessor& preprocessor,
                                        const std::set<LiteralSet>& explanations) {
  for (const auto& explanation : explanations) {
    return check_explanation(preprocessor, explanation);
  }
  return true;
}
#endif
}  // namespace

BoundPreprocessor::BoundPreprocessor(const PredicateAbstractor& predicate_abstractor)
    : config_{predicate_abstractor.config()},
      predicate_abstractor_{predicate_abstractor},
      stats_{config_.with_timings(), "BoundPreprocessor", "Process"} {}

void BoundPreprocessor::AddVariable(const Variable& var) {
  DLINEAR_TRACE_FMT("BoundPreprocessor::AddVariable({})", var);
  theory_bounds_.emplace(var, BoundVector{Infinity::ninfinity(predicate_abstractor_.config()),
                                          Infinity::infinity(predicate_abstractor_.config())});
}

std::set<LiteralSet> BoundPreprocessor::EnableLiterals(const std::vector<Literal>& enabled_literals) {
  std::set<LiteralSet> explanations;
  EnableLiterals(enabled_literals, explanations);
  return explanations;
}
void BoundPreprocessor::EnableLiterals(const std::vector<Literal>& enabled_literals,
                                       std::set<LiteralSet>& explanations) {
  for (const Literal& l : enabled_literals) {
    std::set<LiteralSet> explanation{EnableLiteral(l)};
    if (!explanation.empty()) explanations.insert(explanation.begin(), explanation.end());
  }
}

std::set<LiteralSet> BoundPreprocessor::EnableLiteral(const Literal& lit) {
  std::set<LiteralSet> explanations;
  EnableLiteral(lit, explanations);
  return explanations;
}
void BoundPreprocessor::EnableLiteral(const Literal& lit, std::set<LiteralSet>& explanations) {
  if (enabled_literals_.contains(lit)) return;
  DLINEAR_TRACE_FMT("BoundPreprocessor::EnableLiteral({})", lit);
  const auto& [formula_var, truth] = lit;
  const Formula& formula = predicate_abstractor_[formula_var];

  // If the formula is a simple bound (e.g. x <= 1), immediately add it to the theory_bounds
  if (IsSimpleBound(formula)) {
    // We know there is exactly 1 variable in the formula
    const Variable& var = *formula.GetFreeVariables().cbegin();
    BoundVector& bounds = theory_bounds_.at(var);
    // Add the simple bound to the theory_bound. If a violation is detected, report it immediately
    const BoundIterator violation{bounds.AddBound(GetSimpleBound(lit, formula))};
    if (!violation.empty()) {
      DLINEAR_DEBUG_FMT("BoundPreprocessor::EnableLiteral: {} conflict found", violation.explanation());
      violation.explanations(explanations, lit);
    }
    const mpq_class* const eq_bound = bounds.GetActiveEqualityBound();
    if (eq_bound != nullptr) {
      DLINEAR_ASSERT(!env_.contains(var) || env_[var] == *eq_bound, "No conflict should arise from this assignment");
      env_[var] = *eq_bound;
    }
  }
  enabled_literals_.insert(lit);
  DLINEAR_TRACE_FMT("BoundPreprocessor::EnableLiteral: added constraint {}", lit);
}

void BoundPreprocessor::GetActiveExplanation(const Variable& var, LiteralSet& explanation) {
  const auto it = theory_bounds_.find(var);
  if (it == theory_bounds_.end()) return;
  it->second.GetActiveExplanation(explanation);
}
BoundPreprocessor::Explanations BoundPreprocessor::Process() {
  Explanations explanations;
  Process(enabled_literals_, explanations);
  return explanations;
}
void BoundPreprocessor::Process(Explanations& explanations) { Process(enabled_literals_, explanations); }
BoundPreprocessor::Explanations BoundPreprocessor::Process(const LiteralSet& enabled_literals) {
  Explanations explanations;
  Process(enabled_literals, explanations);
  return explanations;
}
void BoundPreprocessor::Process(const LiteralSet& enabled_literals, Explanations& explanations) {
  DLINEAR_ASSERT(config_.actual_bound_propagation_frequency() != Config::PreprocessingRunningFrequency::NEVER,
                 "Method Process should not be called with a frequency of NEVER");
  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();

  DLINEAR_TRACE_FMT("BoundPreprocessor::Process({})", enabled_literals);
  std::list<Literal> mutable_enabled_formula_vars{enabled_literals.begin(), enabled_literals.end()};

  // Remove all rows that have only one free variable and the != relations, since they can't be propagated
  mutable_enabled_formula_vars.remove_if([this](const Literal& lit) {
    const Formula& formula = predicate_abstractor_[lit.var];
    return formula.GetFreeVariables().size() <= 1 || IsNotEqualTo(formula, lit.truth);
  });

  PropagateConstraints(mutable_enabled_formula_vars, explanations);
  DLINEAR_DEBUG_FMT("BoundPreprocessor::Process: {} conflict found in propagation", explanations.size());
  if (!explanations.empty()) return;

  // Add back all not equal to relations
  for (const Literal& lit : enabled_literals) {
    const Formula& formula = predicate_abstractor_[lit.var];
    if (formula.GetFreeVariables().size() < 2) continue;
    if (IsNotEqualTo(formula, lit.truth)) mutable_enabled_formula_vars.push_back(lit);
  }

  EvaluateFormulas(mutable_enabled_formula_vars, explanations);
  DLINEAR_DEBUG_FMT("BoundPreprocessor::Process: {} conflict found in evaluation", explanations.size());
}

void BoundPreprocessor::SetInfinityBounds(const Variable& var, const mpq_class& lb, const mpq_class& ub) {
  theory_bounds_.insert_or_assign(var, BoundVector{lb, ub});
}

void BoundPreprocessor::Clear() {
  env_ = Environment{};
  for (auto& [var, bounds] : theory_bounds_) bounds.Clear();
  temporary_mpq_vector_.clear();
  enabled_literals_.clear();
}
void BoundPreprocessor::Clear(const BoundPreprocessor& fixed_preprocessor) {
  env_ = fixed_preprocessor.env_;
  theory_bounds_ = fixed_preprocessor.theory_bounds_;
  temporary_mpq_vector_.clear();
  enabled_literals_ = fixed_preprocessor.enabled_literals_;
}

bool BoundPreprocessor::PropagateEqPolynomial(const Literal& lit, const Variable& var_to_propagate,
                                              Explanations& explanations) {
  DLINEAR_TRACE_FMT("BoundPreprocessor::PropagateEqPolynomial({})", lit);

  const Formula& formula = predicate_abstractor_[lit.var];

  DLINEAR_ASSERT_FMT(IsEqualTo(formula, lit.truth), "Lit must encode an equal to relation. Got {}", lit);
  DLINEAR_ASSERT_FMT(formula.IsFlattened(), "The formula must be flattened. Got {}", formula);
  DLINEAR_ASSERT(ShouldPropagateEqPolynomial(lit), "The formula should be propagated");
  DLINEAR_ASSERT(!env_.contains(var_to_propagate), "The variable must not be in the environment yet");
  DLINEAR_ASSERT(!var_to_propagate.is_dummy(), "The variable must be valid");

  LiteralSet explanation{};
  std::vector<Variable> dependencies;
  dependencies.reserve(formula.GetFreeVariables().size() - 1);
  mpq_class rhs{get_constant_value(get_rhs_expression(formula))};
  mpq_class var_coeff{};
  for (const auto& [expr, coeff] : get_expr_to_coeff_map_in_addition(get_lhs_expression(formula))) {
    DLINEAR_ASSERT(is_variable(expr), "All expressions in lhs formula must be variables");
    const Variable& var = get_variable(expr);
    if (var.equal_to(var_to_propagate)) {
      var_coeff = coeff;
      continue;
    }
    rhs -= env_.at(var) * coeff;
    dependencies.emplace_back(var);
  }
  DLINEAR_ASSERT(var_coeff != 0, "The propagated variable coefficient cannot be 0");

  // Calculate the propagated value of the variable
  rhs /= var_coeff;
  //  if (var_propagated.get_name() == "x_11") fmt::println("Propagating {} => {}", var_propagated, lit);
  // Add all the dependencies edges to the graph
  for (const Variable& dependency : dependencies) {
    const LiteralSet dependency_explanation = theory_bounds_.at(dependency).GetActiveEqExplanation();
    explanation.insert(dependency_explanation.begin(), dependency_explanation.end());
    //    if (var_propagated.get_name() == "x_11") fmt::println("{} => {}", dependency, theory_bounds_.at(dependency));
  }
  const auto [env_it, inserted] = env_.insert(var_to_propagate, rhs);
  DLINEAR_ASSERT(inserted, "The variable was not in the environment before");
  //  fmt::println("BoundPreprocessor::PropagateConstraints: {} = {} thanks to constraint {} and {} ({})",
  //  var_propagated,
  //               rhs, lit, dependencies, explanation);
  BoundIterator violation{
      theory_bounds_.at(var_to_propagate).AddBound(env_it->second, LpColBound::B, lit, explanation)};
  if (!violation.empty()) {
    explanation.insert(lit);
    violation.explanation(explanation);
    DLINEAR_DEBUG_FMT("BoundPreprocessor::PropagateConstraints: {} conflict found", explanation);
    explanations.insert(explanation);
    // Remove the propagated constraint from the environment
    env_.erase(env_it);
    //    fmt::println("BoundPreprocessor::PropagateConstraints: {} conflict found", explanation);
    return false;
  }
  DLINEAR_TRACE_FMT("BoundPreprocessor::PropagateConstraints: {} = {} thanks to constraint {} and {}", var_to_propagate,
                    rhs, lit, dependencies);
  return true;
}

bool BoundPreprocessor::PropagateBoundsPolynomial(const dlinear::Literal& lit,
                                                  const dlinear::drake::symbolic::Variable& var_to_propagate,
                                                  const std::vector<Bound>& assumptions,
                                                  dlinear::BoundPreprocessor::Explanations& explanations) {
  BoundVector& bounds = theory_bounds_.at(var_to_propagate);
  DLINEAR_DEV_FMT("Bounds initial: {}", bounds);
  for (auto assumption = assumptions.begin(); assumption != assumptions.end(); ++assumption) {
    BoundIterator violation{bounds.AddBound(*assumption)};
    if (!violation.empty()) {
      for (auto added_assumption = assumptions.begin(); added_assumption != assumption; ++added_assumption) {
        bounds.RemoveBound(*added_assumption);
      }
      return false;
    }
  }
  DLINEAR_DEV_FMT("Bounds assumptions: {}", bounds);

  const bool res = PropagateBoundsPolynomial(lit, var_to_propagate, explanations);
  for (const Bound& assumption : assumptions) bounds.RemoveBound(assumption);
  DLINEAR_DEV_FMT("Bounds after: {}", bounds);
  return res;
}

bool BoundPreprocessor::PropagateBoundsPolynomial(const Literal& lit, const Variable& var_to_propagate,
                                                  Explanations& explanations) {
  DLINEAR_TRACE_FMT("BoundPreprocessor::PropagateInPolynomial({})", lit);

  const Formula& formula = predicate_abstractor_[lit.var];

  DLINEAR_ASSERT(is_relational(formula), "Formula should be a relational relation other than = or !=");
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  DLINEAR_ASSERT(!var_to_propagate.is_dummy(), "The variable must be valid");

  BoundVector& var_bounds = theory_bounds_.at(var_to_propagate);
  LiteralSet l_explanation{};
  LiteralSet u_explanation{};
  std::vector<Variable> dependencies;
  dependencies.reserve(formula.GetFreeVariables().size() - 1);
  mpq_class l_rhs{get_constant_value(get_rhs_expression(formula))};
  mpq_class u_rhs{get_constant_value(get_rhs_expression(formula))};
  mpq_class var_coeff{};
  for (const auto& [expr, coeff] : get_expr_to_coeff_map_in_addition(get_lhs_expression(formula))) {
    DLINEAR_ASSERT(is_variable(expr), "All expressions in lhs formula must be variables");
    const Variable& var = get_variable(expr);
    if (var.equal_to(var_to_propagate)) {
      var_coeff = coeff;
      continue;
    }
    DLINEAR_ASSERT(theory_bounds_.at(var).IsBounded(),
                   "All other variable, except the one being propagated, must be bounded");
    const mpq_class& lower_bound = theory_bounds_.at(var).active_lower_bound();
    const mpq_class& upper_bound = theory_bounds_.at(var).active_upper_bound();
    dependencies.emplace_back(var);
    if (coeff > 0) {
      l_rhs -= upper_bound * coeff;
      u_rhs -= lower_bound * coeff;
      theory_bounds_.at(var).GetActiveBound(upper_bound).explanation(l_explanation);
      theory_bounds_.at(var).GetActiveBound(lower_bound).explanation(u_explanation);
    } else {
      l_rhs -= lower_bound * coeff;
      u_rhs -= upper_bound * coeff;
      theory_bounds_.at(var).GetActiveBound(lower_bound).explanation(l_explanation);
      theory_bounds_.at(var).GetActiveBound(upper_bound).explanation(u_explanation);
    }
  }
  DLINEAR_ASSERT(var_coeff != 0, "The propagated variable coefficient cannot be 0");

  // Calculate the propagated value of the bounds
  l_rhs /= var_coeff;
  u_rhs /= var_coeff;

  if (var_coeff < 0) {
    std::swap(l_rhs, u_rhs);
    std::swap(l_explanation, u_explanation);
  }

  //  fmt::println("PropagateBoundPolynomial: Propagating {}\n{} <= {} <= {}\n{} ({}) <= {} <= ({})", lit, l_rhs,
  //               var_propagated, u_rhs, var_coeff, l_explanation, var_coeff, u_explanation);

  // The formula is an equality relation (==)
  if (IsEqualTo(formula, lit.truth)) {
    // Both bounds are equal. Add an equality bound to the variable
    if (l_rhs == u_rhs) {
      DLINEAR_ASSERT_FMT(l_explanation == u_explanation, "The explanations must be the same. {} vs {} instead",
                         l_explanation, u_explanation);
      const Bound bound{StoreTemporaryMpq(l_rhs), LpColBound::B, lit, l_explanation};
      BoundIterator violation{var_bounds.AddBound(bound)};
      if (!violation.empty()) {
        l_explanation.insert(lit);
        // temporary_mpq_vector_.pop_back();  // Remove the unused bound
        violation.explanation(l_explanation);
        DLINEAR_DEBUG_FMT("BoundPreprocessor::PropagateConstraints2: Eq bound {} conflict found", l_explanation);
        explanations.insert(l_explanation);
        return false;
      }
      DLINEAR_ASSERT(!env_.contains(var_to_propagate) || env_[var_to_propagate] == *var_bounds.GetActiveEqualityBound(),
                     "No conflict should arise from this assignment");
      env_[var_to_propagate] = *var_bounds.GetActiveEqualityBound();
      return true;
    }
    // The two bounds are different. Add the lower and upper bounds to the variable
    const Bound lower_bound{StoreTemporaryMpq(l_rhs), LpColBound::L, lit, l_explanation};
    if (l_rhs >= var_bounds.active_lower_bound()) {
      BoundIterator violation{var_bounds.AddBound(lower_bound)};
      if (!violation.empty()) {
        temporary_mpq_vector_.pop_back();  // Remove the unused lower bound
        l_explanation.insert(lit);
        violation.explanation(l_explanation);
        DLINEAR_DEBUG_FMT("BoundPreprocessor::PropagateConstraints2: Lower bound {} conflict found", l_explanation);
        explanations.insert(l_explanation);
        return false;
      }
    } else {
      temporary_mpq_vector_.pop_back();  // Remove the unused lower bound
    }
    const Bound upper_bound{StoreTemporaryMpq(u_rhs), LpColBound::U, lit, u_explanation};
    if (u_rhs <= var_bounds.active_upper_bound()) {
      BoundIterator violation{var_bounds.AddBound(upper_bound)};
      if (!violation.empty()) {
        temporary_mpq_vector_.pop_back();  // Remove the unused upper bound
        // Also remove the unused lower bound, if had been added in the previous step
        if (var_bounds.RemoveBound(lower_bound)) temporary_mpq_vector_.pop_back();
        u_explanation.insert(lit);
        violation.explanation(u_explanation);
        DLINEAR_DEBUG_FMT("BoundPreprocessor::PropagateConstraints2: Upper bound {} conflict found", u_explanation);
        explanations.insert(u_explanation);
        return false;
      }
    } else {
      temporary_mpq_vector_.pop_back();  // Remove the unused upper bound
    }
    DLINEAR_TRACE_FMT("BoundPreprocessor::PropagateConstraints: {} = [{}, {}] thanks to constraint {} and {}",
                      var_to_propagate, l_rhs, u_rhs, lit, dependencies);
    //    fmt::println("BoundPreprocessor::PropagateConstraints: {} = [{}, {}] thanks to constraint {} and {}",
    //                 var_propagated, l_rhs, u_rhs, lit, dependencies);
    const mpq_class* const eq_bound = var_bounds.GetActiveEqualityBound();
    if (eq_bound != nullptr) {
      DLINEAR_ASSERT(!env_.contains(var_to_propagate) || env_[var_to_propagate] == *eq_bound,
                     "No conflict should arise from this assignment");
      env_[var_to_propagate] = *eq_bound;
    }
    return true;
  }

  Bound bound;
  // Add the bound on the single unbounded variable based on the upper and lower bound computed over the polynomial
  if (var_coeff > 0) {
    if (IsGreaterThan(formula, lit.truth)) {
      bound = {StoreTemporaryMpq(l_rhs), LpColBound::SL, lit, l_explanation};
    } else if (IsGreaterThanOrEqualTo(formula, lit.truth)) {
      bound = {StoreTemporaryMpq(l_rhs), LpColBound::L, lit, l_explanation};
    } else if (IsLessThan(formula, lit.truth)) {
      bound = {StoreTemporaryMpq(u_rhs), LpColBound::SU, lit, u_explanation};
    } else {
      DLINEAR_ASSERT(IsLessThanOrEqualTo(formula, lit.truth), "The formula must be a less than or equal to relation");
      bound = {StoreTemporaryMpq(u_rhs), LpColBound::U, lit, u_explanation};
    }
  } else {
    DLINEAR_ASSERT(var_coeff < 0, "The coefficient must be less than 0");
    if (IsGreaterThan(formula, lit.truth)) {
      bound = {StoreTemporaryMpq(u_rhs), LpColBound::SU, lit, u_explanation};
    } else if (IsGreaterThanOrEqualTo(formula, lit.truth)) {
      bound = {StoreTemporaryMpq(u_rhs), LpColBound::U, lit, u_explanation};
    } else if (IsLessThan(formula, lit.truth)) {
      bound = {StoreTemporaryMpq(l_rhs), LpColBound::SL, lit, l_explanation};
    } else {
      DLINEAR_ASSERT(IsLessThanOrEqualTo(formula, lit.truth), "The formula must be a less than or equal to relation");
      bound = {StoreTemporaryMpq(l_rhs), LpColBound::L, lit, l_explanation};
    }
  }
  //  fmt::println("BoundPreprocessor::PropagateConstraints: {} = [{}, {}] thanks to constraint {} and {}",
  //  var_propagated,
  //               l_rhs, u_rhs, lit, dependencies);
  BoundIterator violation{var_bounds.AddBound(bound)};
  if (!violation.empty()) {
    bound.explanation.insert(lit);
    temporary_mpq_vector_.pop_back();  // Remove the unused bound
    violation.explanation(bound.explanation);
    DLINEAR_DEBUG_FMT("BoundPreprocessor::PropagateConstraints: {} conflict found", bound.explanation);
    explanations.insert(bound.explanation);
    return false;
  }
  DLINEAR_TRACE_FMT("BoundPreprocessor::PropagateConstraints: {} = [{}, {}] thanks to constraint {} and {}",
                    var_to_propagate, l_rhs, u_rhs, lit, dependencies);
  const mpq_class* const eq_bound = var_bounds.GetActiveEqualityBound();
  if (eq_bound != nullptr) {
    DLINEAR_ASSERT(!env_.contains(var_to_propagate) || env_[var_to_propagate] == *eq_bound,
                   "No conflict should arise from this assignment");
    env_[var_to_propagate] = *eq_bound;
  }
  return true;
}

void BoundPreprocessor::PropagateConstraints(std::list<Literal>& enabled_literals, Explanations& explanations) {
  DLINEAR_TRACE("BoundPreprocessor::PropagateConstraints()");
  // TODO(tend): reintroduce PropagateEqBinConstraints();
  if (config_.actual_bound_propagation_type() < Config::BoundPropagationType::EQ_POLYNOMIAL) return;
  PropagateEqConstraints(enabled_literals, explanations);
  if (!explanations.empty() || config_.actual_bound_propagation_type() < Config::BoundPropagationType::BOUND_POLYNOMIAL)
    return;
  PropagateBoundConstraints(enabled_literals, explanations);
}
void BoundPreprocessor::PropagateEqConstraints(std::list<Literal>& enabled_literals, Explanations& explanations) {
  DLINEAR_TRACE_FMT("BoundPreprocessor::PropagateEqConstraints({})", enabled_literals);
  bool continue_propagating;
  // While we still have constraints to propagate...
  do {
    continue_propagating = false;
    for (auto it = enabled_literals.begin(); it != enabled_literals.end();) {
      const Literal& lit = *it;
      const Variable* const var_to_propagate = ShouldPropagateEqPolynomial(lit);
      if (var_to_propagate == nullptr) {
        ++it;
        continue;
      }
      // Try to propagate the bounds to the variable. If a conflict is detected, update the explanation
      PropagateEqPolynomial(lit, *var_to_propagate, explanations);
      // Since we did a propagation (with a violation or not), delete the literal.
      // Also signal that the other literals could have been updated. Therefore, continue the propagation
      continue_propagating = true;
      it = enabled_literals.erase(it);
    }
  } while (continue_propagating && explanations.empty());
  DLINEAR_TRACE_FMT("BoundPreprocessor::PropagateEqConstraints: explanation -> {}", explanations);
}
void BoundPreprocessor::PropagateBoundConstraints(std::list<Literal>& enabled_literals, Explanations& explanations) {
  DLINEAR_TRACE_FMT("BoundPreprocessor::PropagateBoundConstraints({})", enabled_literals);
  bool continue_propagating;
  // While we still have constraints to propagate...
  do {
    continue_propagating = false;
    for (auto it = enabled_literals.begin(); it != enabled_literals.end();) {
      const Literal& lit = *it;
      // Check if there is a variable candidate for the propagation
      const Variable* const var_to_propagate = ShouldPropagateBoundsPolynomial(lit);
      if (var_to_propagate == nullptr) {
        ++it;
        continue;
      }
      // Try to propagate the bounds to the variable. If a conflict is detected, update the explanation
      PropagateBoundsPolynomial(lit, *var_to_propagate, explanations);
      // Since we did a propagation (with a violation or not), delete the literal.
      // Also signal that the other literals could have been updated. Therefore, continue the propagation
      continue_propagating = true;
      it = enabled_literals.erase(it);
    }
  } while (continue_propagating && explanations.empty());
  DLINEAR_TRACE_FMT("BoundPreprocessor::PropagateBoundConstraints: explanation -> {}", explanations);
}

void BoundPreprocessor::EvaluateFormulas(std::list<Literal>& enabled_literals, Explanations& explanations) {
  DLINEAR_ASSERT(explanations.empty(), "The explanations vector must be empty");
  DLINEAR_TRACE("BoundPreprocessor::EvaluateFormulas()");
  for (const Literal& lit : enabled_literals) {
    if (!ShouldEvaluate(lit)) continue;
    const Formula& formula = predicate_abstractor_[lit.var];
    const bool satisfied = formula.Evaluate(env_) == lit.truth;
    if (!satisfied) {
      DLINEAR_DEBUG_FMT("BoundPreprocessor::EvaluateFormulas: {} => FAIL", lit);
      FormulaViolationExplanation(lit, formula, explanations);
    }
  }
}

void BoundPreprocessor::FormulaViolationExplanation(const Literal& lit, const Formula& formula,
                                                    Explanations& explanations) {
  DLINEAR_TRACE_FMT("BoundPreprocessor::FormulaViolationExplanation({})", formula);
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

bool BoundPreprocessor::ShouldEvaluate(const Literal& lit) const {
  DLINEAR_TRACE_FMT("BoundPreprocessor::ShouldEvaluate({})", lit);
  const Formula& formula = predicate_abstractor_[lit.var];
  return ShouldEvaluate(formula);
}
bool BoundPreprocessor::ShouldEvaluate(const Formula& formula) const {
  DLINEAR_TRACE_FMT("BoundPreprocessor::ShouldEvaluate({})", formula);
  // All free variables must be in the environment
  return std::all_of(formula.GetFreeVariables().begin(), formula.GetFreeVariables().end(),
                     [this](const Variable& v) { return env_.contains(v); });
}

const Variable* BoundPreprocessor::ShouldPropagateEqPolynomial(const Literal& lit) const {
  DLINEAR_TRACE_FMT("BoundPreprocessor::ShouldPropagateEqPolynomial({})", lit);
  const auto& [formula_var, truth] = lit;
  const Formula& formula = predicate_abstractor_[formula_var];
  // There must be exactly two free variables and an equality relation between them
  if (!IsEqualTo(formula, truth)) return nullptr;
  return ShouldPropagateEqPolynomial(formula);
}
const Variable* BoundPreprocessor::ShouldPropagateEqPolynomial(const Formula& formula) const {
  DLINEAR_TRACE_FMT("BoundPreprocessor::ShouldPropagateEqPolynomial({})", formula);
  // There must be exactly two free variables and an equality relation between them
  if (!is_equal_to(formula) && !is_not_equal_to(formula)) return nullptr;
  if (formula.GetFreeVariables().size() < 2) return nullptr;
  DLINEAR_ASSERT(is_addition(get_lhs_expression(formula)), "lhs expression must be an addition");

  // The formula must be of the form 'a1x1 + a2x2 + ... + anxn + c = b', with ai,b != 0
  const Variable* missing_var = nullptr;
  for (const auto& [expr, coeff] : get_expr_to_coeff_map_in_addition(get_lhs_expression(formula))) {
    DLINEAR_ASSERT(is_variable(expr), "All expressions in lhs formula must be variables");
    if (env_.find(get_variable(expr)) != env_.cend()) continue;
    // There is more than one variable missing its value
    if (missing_var != nullptr) return nullptr;
    missing_var = &get_variable(expr);
  }
  return missing_var;
}
const Variable* BoundPreprocessor::ShouldPropagateBoundsPolynomial(const Literal& lit) const {
  DLINEAR_TRACE_FMT("BoundPreprocessor::ShouldPropagateInPolynomial({})", lit);
  const auto& [formula_var, truth] = lit;
  const Formula& formula = predicate_abstractor_[formula_var];
  // There must be exactly two free variables and an equality relation between them
  if (!is_relational(formula)) return nullptr;
  if (IsNotEqualTo(formula, truth)) return nullptr;
  return ShouldPropagateBoundsPolynomial(formula);
}
const Variable* BoundPreprocessor::ShouldPropagateBoundsPolynomial(const Formula& formula) const {
  DLINEAR_TRACE_FMT("BoundPreprocessor::ShouldPropagateInPolynomial({})", formula);
  // There must be more than two free variables and an inequality relation between them
  if (!is_relational(formula)) return nullptr;
  if (formula.GetFreeVariables().size() < 2) return nullptr;
  DLINEAR_ASSERT(is_addition(get_lhs_expression(formula)), "lhs expression must be an addition");

  // TODO(tend): being naive, this approach will not propagate some bounds that could be propagated
  //  since it forces the dependency variables to be bounded both ways for propagation
  // The formula must be of the form 'a1x1 + a2x2 + ... + anxn + c <=> b', with ai,b != 0 and <=> in {<, <=, >, >=, !=}
  const Variable* missing_var = nullptr;
  for (const auto& [expr, coeff] : get_expr_to_coeff_map_in_addition(get_lhs_expression(formula))) {
    DLINEAR_ASSERT(is_variable(expr), "All expressions in lhs formula must be variables");
    const Variable& var = get_variable(expr);
    const auto it = theory_bounds_.find(var);
    if (it == theory_bounds_.end() || !it->second.IsBounded()) {
      // There is more than one variable missing its value
      if (missing_var != nullptr) return nullptr;
      missing_var = &var;
    }
  }
  return missing_var;
}

std::pair<Variable, Variable> BoundPreprocessor::ExtractBoundEdge(const Formula& formula) const {
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

mpq_class BoundPreprocessor::ExtractEqBoundCoefficient(const Formula& formula) const {
  DLINEAR_ASSERT(is_equal_to(formula), "Formula should be an equality relation");
  DLINEAR_ASSERT(formula.GetFreeVariables().size() == 2, "Formula should have exactly two free variables");
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  const Expression& lhs = get_lhs_expression(formula);

  const std::map<Expression, mpq_class>& map = get_expr_to_coeff_map_in_addition(lhs);
  DLINEAR_ASSERT(map.size() == 2, "Expression should have exactly two variables");
  DLINEAR_ASSERT(get_constant_value(get_rhs_expression(formula)) == 0, "The right-hand side must be 0");

  return -(std::next(map.cbegin())->second) / map.cbegin()->second;
}

const mpq_class* BoundPreprocessor::StoreTemporaryMpq(const mpq_class& value) {
  temporary_mpq_vector_.emplace_back(value);
  return &temporary_mpq_vector_.back();
}
Bound BoundPreprocessor::GetSimpleBound(const dlinear::Literal& lit) const {
  return GetSimpleBound(lit, predicate_abstractor_[lit.var]);
}
Bound BoundPreprocessor::GetSimpleBound(const Literal& lit, const Formula& formula) const {
  DLINEAR_ASSERT(IsSimpleBound(formula), "Formula must be a simple bound");
  const Expression& lhs{get_lhs_expression(formula)};
  const Expression& rhs{get_rhs_expression(formula)};
  if (IsEqualTo(formula, lit.truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {&get_constant_value(rhs), LpColBound::B, lit};
    if (is_constant(lhs) && is_variable(rhs)) return {&get_constant_value(lhs), LpColBound::B, lit};
  }
  if (IsGreaterThan(formula, lit.truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {&get_constant_value(rhs), LpColBound::SL, lit};
    if (is_constant(lhs) && is_variable(rhs)) return {&get_constant_value(lhs), LpColBound::SU, lit};
  }
  if (IsGreaterThanOrEqualTo(formula, lit.truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {&get_constant_value(rhs), LpColBound::L, lit};
    if (is_constant(lhs) && is_variable(rhs)) return {&get_constant_value(lhs), LpColBound::U, lit};
  }
  if (IsLessThan(formula, lit.truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {&get_constant_value(rhs), LpColBound::SU, lit};
    if (is_constant(lhs) && is_variable(rhs)) return {&get_constant_value(lhs), LpColBound::SL, lit};
  }
  if (IsLessThanOrEqualTo(formula, lit.truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {&get_constant_value(rhs), LpColBound::U, lit};
    if (is_constant(lhs) && is_variable(rhs)) return {&get_constant_value(lhs), LpColBound::L, lit};
  }
  if (IsNotEqualTo(formula, lit.truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {&get_constant_value(rhs), LpColBound::D, lit};
    if (is_constant(lhs) && is_variable(rhs)) return {&get_constant_value(lhs), LpColBound::D, lit};
  }
  DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
}

bool BoundPreprocessor::IsSimpleBound(const Formula& formula) {
  // Formula must be a relational formula: `lhs <= rhs`, `lhs >= rhs`, `lhs == rhs` or `lhs != rhs`.
  if (!is_relational(formula)) return false;
  // The number of variables must be exactly one
  if (formula.GetFreeVariables().size() != 1) return false;

  // one between lhs and rhs must be a constant and the other must be a variable.
  const Expression& lhs{get_lhs_expression(formula)};
  const Expression& rhs{get_rhs_expression(formula)};
  return ((is_constant(lhs) && is_variable(rhs)) || (is_variable(lhs) && is_constant(rhs)));
}

bool BoundPreprocessor::IsEqualTo(const Formula& formula, const bool truth) {
  return truth ? is_equal_to(formula) : is_not_equal_to(formula);
}

bool BoundPreprocessor::IsNotEqualTo(const Formula& formula, const bool truth) {
  return truth ? is_not_equal_to(formula) : is_equal_to(formula);
}

bool BoundPreprocessor::IsGreaterThan(const Formula& formula, const bool truth) {
  return truth ? is_greater_than(formula) : is_less_than_or_equal_to(formula);
}

bool BoundPreprocessor::IsLessThan(const Formula& formula, const bool truth) {
  return truth ? is_less_than(formula) : is_greater_than_or_equal_to(formula);
}

bool BoundPreprocessor::IsGreaterThanOrEqualTo(const Formula& formula, const bool truth) {
  return truth ? is_greater_than_or_equal_to(formula) : is_less_than(formula);
}

bool BoundPreprocessor::IsLessThanOrEqualTo(const Formula& formula, const bool truth) {
  return truth ? is_less_than_or_equal_to(formula) : is_greater_than(formula);
}

void BoundPreprocessor::GetExplanation(const Variable& var, LiteralSet& explanation) {
  const auto it = theory_bounds_.find(var);
  if (it == theory_bounds_.end()) return;
  it->second.GetActiveExplanation(explanation);
}

std::ostream& operator<<(std::ostream& os, const BoundPreprocessor& preprocessor) {
  return os << "BoundPreprocessor{" << "env_ = " << preprocessor.env() << ", "
            << "theory_bounds_ = " << preprocessor.theory_bounds() << "}";
}

}  // namespace dlinear
