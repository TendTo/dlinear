/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "BoundedPolynomialPreprocessor.h"

#include <algorithm>
#include <cstddef>
#include <iterator>
#include <list>
#include <ostream>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/theory_solver/qf_lra/QfLraTheorySolver.h"
// #include "dlinear/util/Infinity.h"
#include "dlinear/util/error.h"

namespace dlinear {

BoundedPolynomialPreprocessor::BoundedPolynomialPreprocessor(const TheorySolver& theory_solver,
                                                             const std::shared_ptr<BoundVectorMap>& var_bounds,
                                                             const std::shared_ptr<Environment>& env,
                                                             const std::string& class_name)
    : TheoryPreprocessor{theory_solver, class_name}, var_bounds_{var_bounds}, env_{env} {
  DLINEAR_ASSERT(var_bounds_ != nullptr, "The var_bounds must not be null");
  DLINEAR_ASSERT(env_ != nullptr, "The env must not be null");
}

void BoundedPolynomialPreprocessor::AddVariable(const Variable& var) {
  DLINEAR_TRACE_FMT("BoundCheckerPreprocessor::AddVariable({})", var);
  //  var_bounds_->emplace(var, BoundVector{Infinity::ninfinity(predicate_abstractor_.config()),
  //                                          Infinity::infinity(predicate_abstractor_.config())});
}

bool BoundedPolynomialPreprocessor::EnableLiteral(const Literal& lit, const ConflictCallback&) {
  DLINEAR_TRACE_FMT("BoundedPolynomialPreprocessor::EnableConstraint({})", lit);
  const Formula& formula = theory_solver_.predicate_abstractor()[lit.var];
  // If the literal only contains one variable, or it's a not-equal-to relationship there is no need to evaluate it
  if (formula.GetFreeVariables().size() <= 1 || IsNotEqualTo(formula, lit.truth)) return true;
  enabled_literals_.emplace(lit);
  return true;
}

void BoundedPolynomialPreprocessor::SetEnvironmentFromBounds() {
  for (const auto& [var, bound] : *var_bounds_) {
    const mpq_class* const active_bound = bound.GetActiveEqualityBound();
    if (active_bound == nullptr) continue;
    if (env_->contains(var)) {
      DLINEAR_ASSERT(env_->at(var) == *active_bound, "No conflict should arise from this assignment");
      continue;
    }
    (*env_)[var] = *active_bound;
  }
}

bool BoundedPolynomialPreprocessor::ProcessCore(const ConflictCallback& conflict_cb) {
  DLINEAR_TRACE("BoundedPolynomialPreprocessor::Process()");
  // Sync the local var bounds with the ones from the theory solver if it is still empty
  if (var_bounds_->empty()) *var_bounds_ = static_cast<const QfLraTheorySolver&>(theory_solver_).vars_bounds();
  // Sync the environment with the active equality bounds from the var bounds if it is still empty
  if (env_->empty()) SetEnvironmentFromBounds();
  std::list<Literal> enabled_literals(enabled_literals_.begin(), enabled_literals_.end());
  const bool no_conflict =
      PropagateEqConstraints(enabled_literals, conflict_cb) && PropagateBoundConstraints(enabled_literals, conflict_cb);
  DLINEAR_DEBUG_FMT("FormulaEvaluatorPreprocessor::Process no conflict found -> {}", no_conflict);
  return no_conflict;
}
Config::ExecutionStep BoundedPolynomialPreprocessor::run_on_step() const {
  return theory_solver_.config().actual_bounded_polynomial_preprocess_step();
}

void BoundedPolynomialPreprocessor::Backtrack() {
  if (!env_->empty()) *env_ = Environment{};
  var_bounds_->clear();
  enabled_literals_.clear();
}

bool BoundedPolynomialPreprocessor::PropagateEqPolynomial(const Literal& lit, const Variable& var_to_propagate,
                                                          const ConflictCallback& conflict_cb) {
  DLINEAR_TRACE_FMT("BoundCheckerPreprocessor::PropagateEqPolynomial({})", lit);

  const Formula& formula = theory_solver_.predicate_abstractor()[lit.var];

  DLINEAR_ASSERT_FMT(IsEqualTo(formula, lit.truth), "Lit must encode an equal to relation. Got {}", lit);
  DLINEAR_ASSERT_FMT(formula.IsFlattened(), "The formula must be flattened. Got {}", formula);
  DLINEAR_ASSERT(ShouldPropagateEqPolynomial(lit), "The formula should be propagated");
  DLINEAR_ASSERT(!env_->contains(var_to_propagate), "The variable must not be in the environment yet");
  DLINEAR_ASSERT(!var_to_propagate.is_dummy(), "The variable must be valid");

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
    rhs -= env_->at(var) * coeff;
    dependencies.emplace_back(var);
  }
  DLINEAR_ASSERT(var_coeff != 0, "The propagated variable coefficient cannot be 0");

  // Calculate the propagated value of the variable
  rhs /= var_coeff;

  // Insert the new value of the variable in the environment
  const auto [env_it, inserted] = env_->insert(var_to_propagate, rhs);
  DLINEAR_ASSERT(inserted, "The variable was not in the environment before");

  // Prepare the bound to add
  Bound bound{&env_it->second, LpColBound::B, lit};

  // Add all the dependencies as explanations for this bound
  for (const Variable& dependency : dependencies) {
    const LiteralSet dependency_explanation = var_bounds_->at(dependency).GetActiveEqExplanation();
    bound.explanation.insert(dependency_explanation.begin(), dependency_explanation.end());
  }

  if (const bool added = var_bounds_->at(var_to_propagate).AddBound(bound, conflict_cb); !added) {
    DLINEAR_DEBUG_FMT("BoundCheckerPreprocessor::PropagateConstraints: conflict found on {}", lit);
    // Remove the propagated constraint from the environment
    env_->erase(env_it);
    return false;
  }
  DLINEAR_TRACE_FMT("BoundCheckerPreprocessor::PropagateConstraints: {} = {} thanks to constraint {} and {}",
                    var_to_propagate, rhs, lit, dependencies);
  return true;
}

bool BoundedPolynomialPreprocessor::PropagateBoundsPolynomial(const Literal& lit, const Variable& var_to_propagate,
                                                              const std::vector<Bound>& assumptions,
                                                              const ConflictCallback& conflict_cb) {
  BoundVector& bounds = var_bounds_->at(var_to_propagate);
  DLINEAR_DEV_FMT("Bounds initial: {}", bounds);
  for (auto assumption = assumptions.begin(); assumption != assumptions.end(); ++assumption) {
    if (BoundIterator violation{bounds.AddBound(*assumption)}; !violation.empty()) {
      for (auto added_assumption = assumptions.begin(); added_assumption != assumption; ++added_assumption) {
        bounds.RemoveBound(*added_assumption);
      }
      return false;
    }
  }
  DLINEAR_DEV_FMT("Bounds assumptions: {}", bounds);

  const bool res = PropagateBoundsPolynomial(lit, var_to_propagate, conflict_cb);
  for (const Bound& assumption : assumptions) bounds.RemoveBound(assumption);
  DLINEAR_DEV_FMT("Bounds after: {}", bounds);
  return res;
}

bool BoundedPolynomialPreprocessor::PropagateBoundsPolynomial(const Literal& lit, const Variable& var_to_propagate,
                                                              const ConflictCallback& conflict_cb) {
  DLINEAR_TRACE_FMT("BoundCheckerPreprocessor::PropagateInPolynomial({})", lit);

  const Formula& formula = theory_solver_.predicate_abstractor()[lit.var];

  DLINEAR_ASSERT(is_relational(formula), "Formula should be a relational relation other than = or !=");
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  DLINEAR_ASSERT(!var_to_propagate.is_dummy(), "The variable must be valid");

  BoundVector& var_bounds = var_bounds_->at(var_to_propagate);
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
    DLINEAR_ASSERT(var_bounds_->at(var).IsBounded(),
                   "All other variable, except the one being propagated, must be bounded");
    const mpq_class& lower_bound = var_bounds_->at(var).active_lower_bound();
    const mpq_class& upper_bound = var_bounds_->at(var).active_upper_bound();
    dependencies.emplace_back(var);
    if (coeff > 0) {
      l_rhs -= upper_bound * coeff;
      u_rhs -= lower_bound * coeff;
      var_bounds_->at(var).GetActiveBound(upper_bound).explanation(l_explanation);
      var_bounds_->at(var).GetActiveBound(lower_bound).explanation(u_explanation);
    } else {
      l_rhs -= lower_bound * coeff;
      u_rhs -= upper_bound * coeff;
      var_bounds_->at(var).GetActiveBound(lower_bound).explanation(l_explanation);
      var_bounds_->at(var).GetActiveBound(upper_bound).explanation(u_explanation);
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

  // The formula is an equality relation (==)
  if (IsEqualTo(formula, lit.truth)) {
    // Both bounds are equal. Add an equality bound to the variable
    if (l_rhs == u_rhs) {
      DLINEAR_ASSERT_FMT(l_explanation == u_explanation, "The explanations must be the same. {} vs {} instead",
                         l_explanation, u_explanation);
      const Bound bound{StoreTemporaryMpq(l_rhs), LpColBound::B, lit, l_explanation};
      if (BoundIterator violation{var_bounds.AddBound(bound)}; !violation.empty()) {
        l_explanation.insert(lit);
        // temporary_mpq_vector_.pop_back();  // Remove the unused bound
        violation.explanation(l_explanation);
        DLINEAR_DEBUG_FMT("BoundCheckerPreprocessor::PropagateConstraints2: Eq bound {} conflict found", l_explanation);
        conflict_cb(l_explanation);
        return false;
      }
      DLINEAR_ASSERT(
          !env_->contains(var_to_propagate) || env_->at(var_to_propagate) == *var_bounds.GetActiveEqualityBound(),
          "No conflict should arise from this assignment");
      (*env_)[var_to_propagate] = *var_bounds.GetActiveEqualityBound();
      return true;
    }
    // The two bounds are different. Add the lower and upper bounds to the variable
    const Bound lower_bound{StoreTemporaryMpq(l_rhs), LpColBound::L, lit, l_explanation};
    if (l_rhs >= var_bounds.active_lower_bound()) {
      if (BoundIterator violation{var_bounds.AddBound(lower_bound)}; !violation.empty()) {
        temporary_mpq_vector_.pop_back();  // Remove the unused lower bound
        l_explanation.insert(lit);
        violation.explanation(l_explanation);
        DLINEAR_DEBUG_FMT("BoundCheckerPreprocessor::PropagateConstraints2: Lower bound {} conflict found",
                          l_explanation);
        conflict_cb(l_explanation);
        return false;
      }
    } else {
      temporary_mpq_vector_.pop_back();  // Remove the unused lower bound
    }
    const Bound upper_bound{StoreTemporaryMpq(u_rhs), LpColBound::U, lit, u_explanation};
    if (u_rhs <= var_bounds.active_upper_bound()) {
      if (BoundIterator violation{var_bounds.AddBound(upper_bound)}; !violation.empty()) {
        temporary_mpq_vector_.pop_back();  // Remove the unused upper bound
        // Also remove the unused lower bound, if had been added in the previous step
        if (var_bounds.RemoveBound(lower_bound)) temporary_mpq_vector_.pop_back();
        u_explanation.insert(lit);
        violation.explanation(u_explanation);
        DLINEAR_DEBUG_FMT("BoundCheckerPreprocessor::PropagateConstraints2: Upper bound {} conflict found",
                          u_explanation);
        conflict_cb(u_explanation);
        return false;
      }
    } else {
      temporary_mpq_vector_.pop_back();  // Remove the unused upper bound
    }
    DLINEAR_TRACE_FMT("BoundCheckerPreprocessor::PropagateConstraints: {} = [{}, {}] thanks to constraint {} and {}",
                      var_to_propagate, l_rhs, u_rhs, lit, dependencies);
    if (const mpq_class* const eq_bound = var_bounds.GetActiveEqualityBound(); eq_bound != nullptr) {
      DLINEAR_ASSERT(!env_->contains(var_to_propagate) || env_->at(var_to_propagate) == *eq_bound,
                     "No conflict should arise from this assignment");
      (*env_)[var_to_propagate] = *eq_bound;
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
  //  fmt::println("BoundCheckerPreprocessor::PropagateConstraints: {} = [{}, {}] thanks to constraint {} and {}",
  //  var_propagated,
  //               l_rhs, u_rhs, lit, dependencies);
  if (BoundIterator violation{var_bounds.AddBound(bound)}; !violation.empty()) {
    bound.explanation.insert(lit);
    temporary_mpq_vector_.pop_back();  // Remove the unused bound
    violation.explanation(bound.explanation);
    DLINEAR_DEBUG_FMT("BoundCheckerPreprocessor::PropagateConstraints: {} conflict found", bound.explanation);
    conflict_cb(bound.explanation);
    return false;
  }
  DLINEAR_TRACE_FMT("BoundCheckerPreprocessor::PropagateConstraints: {} = [{}, {}] thanks to constraint {} and {}",
                    var_to_propagate, l_rhs, u_rhs, lit, dependencies);
  if (const mpq_class* const eq_bound = var_bounds.GetActiveEqualityBound(); eq_bound != nullptr) {
    DLINEAR_ASSERT(!env_->contains(var_to_propagate) || env_->at(var_to_propagate) == *eq_bound,
                   "No conflict should arise from this assignment");
    (*env_)[var_to_propagate] = *eq_bound;
  }
  return true;
}

bool BoundedPolynomialPreprocessor::PropagateEqConstraints(std::list<Literal>& enabled_literals,
                                                           const ConflictCallback& conflict_cb) {
  DLINEAR_TRACE_FMT("BoundCheckerPreprocessor::PropagateEqConstraints({})", enabled_literals);
  bool continue_propagating;
  bool no_conflict = true;
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
      no_conflict &= PropagateEqPolynomial(lit, *var_to_propagate, conflict_cb);
      // Since we did a propagation (with a violation or not), delete the literal.
      // Also signal that the other literals could have been updated. Therefore, continue the propagation
      continue_propagating = true;
      it = enabled_literals.erase(it);
    }
  } while (continue_propagating && no_conflict);
  DLINEAR_TRACE_FMT("BoundCheckerPreprocessor::PropagateEqConstraints: no conflict -> {}", no_conflict);
  return no_conflict;
}
bool BoundedPolynomialPreprocessor::PropagateBoundConstraints(std::list<Literal>& enabled_literals,
                                                              const ConflictCallback& conflict_cb) {
  DLINEAR_TRACE_FMT("BoundCheckerPreprocessor::PropagateBoundConstraints({})", enabled_literals);
  bool continue_propagating;
  bool no_conflict = true;
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
      no_conflict &= PropagateBoundsPolynomial(lit, *var_to_propagate, conflict_cb);
      // Since we did a propagation (with a violation or not), delete the literal.
      // Also signal that the other literals could have been updated. Therefore, continue the propagation
      continue_propagating = true;
      it = enabled_literals.erase(it);
    }
  } while (continue_propagating && no_conflict);
  DLINEAR_TRACE_FMT("BoundCheckerPreprocessor::PropagateBoundConstraints: no conflict -> {}", no_conflict);
  return no_conflict;
}

const Variable* BoundedPolynomialPreprocessor::ShouldPropagateEqPolynomial(const Literal& lit) const {
  DLINEAR_TRACE_FMT("BoundCheckerPreprocessor::ShouldPropagateEqPolynomial({})", lit);
  const auto& [formula_var, truth] = lit;
  const Formula& formula = theory_solver_.predicate_abstractor()[formula_var];
  // There must be exactly two free variables and an equality relation between them
  if (!IsEqualTo(formula, truth)) return nullptr;
  return ShouldPropagateEqPolynomial(formula);
}
const Variable* BoundedPolynomialPreprocessor::ShouldPropagateEqPolynomial(const Formula& formula) const {
  DLINEAR_TRACE_FMT("BoundCheckerPreprocessor::ShouldPropagateEqPolynomial({})", formula);
  // There must be exactly two free variables and an equality relation between them
  if (!is_equal_to(formula) && !is_not_equal_to(formula)) return nullptr;
  if (formula.GetFreeVariables().size() < 2) return nullptr;
  DLINEAR_ASSERT(is_addition(get_lhs_expression(formula)), "lhs expression must be an addition");

  // The formula must be of the form 'a1x1 + a2x2 + ... + anxn + c = b', with ai,b != 0
  const Variable* missing_var = nullptr;
  for (const auto& [expr, coeff] : get_expr_to_coeff_map_in_addition(get_lhs_expression(formula))) {
    DLINEAR_ASSERT(is_variable(expr), "All expressions in lhs formula must be variables");
    if (env_->contains(get_variable(expr))) continue;
    // There is more than one variable missing its value
    if (missing_var != nullptr) return nullptr;
    missing_var = &get_variable(expr);
  }
  return missing_var;
}
const Variable* BoundedPolynomialPreprocessor::ShouldPropagateBoundsPolynomial(const Literal& lit) const {
  DLINEAR_TRACE_FMT("BoundCheckerPreprocessor::ShouldPropagateInPolynomial({})", lit);
  const auto& [formula_var, truth] = lit;
  const Formula& formula = theory_solver_.predicate_abstractor()[formula_var];
  // There must be exactly two free variables and an equality relation between them
  if (!is_relational(formula)) return nullptr;
  if (IsNotEqualTo(formula, truth)) return nullptr;
  return ShouldPropagateBoundsPolynomial(formula);
}
const Variable* BoundedPolynomialPreprocessor::ShouldPropagateBoundsPolynomial(const Formula& formula) const {
  DLINEAR_TRACE_FMT("BoundCheckerPreprocessor::ShouldPropagateInPolynomial({})", formula);
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
    if (const auto it = var_bounds_->find(var); it == var_bounds_->end() || !it->second.IsBounded()) {
      // There is more than one variable missing its value
      if (missing_var != nullptr) return nullptr;
      missing_var = &var;
    }
  }
  return missing_var;
}

std::pair<Variable, Variable> BoundedPolynomialPreprocessor::ExtractBoundEdge(const Formula& formula) const {
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

mpq_class BoundedPolynomialPreprocessor::ExtractEqBoundCoefficient(const Formula& formula) const {
  DLINEAR_ASSERT(is_equal_to(formula), "Formula should be an equality relation");
  DLINEAR_ASSERT(formula.GetFreeVariables().size() == 2, "Formula should have exactly two free variables");
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  const Expression& lhs = get_lhs_expression(formula);

  const std::map<Expression, mpq_class>& map = get_expr_to_coeff_map_in_addition(lhs);
  DLINEAR_ASSERT(map.size() == 2, "Expression should have exactly two variables");
  DLINEAR_ASSERT(get_constant_value(get_rhs_expression(formula)) == 0, "The right-hand side must be 0");

  return -(std::next(map.cbegin())->second) / map.cbegin()->second;
}

const mpq_class* BoundedPolynomialPreprocessor::StoreTemporaryMpq(const mpq_class& value) {
  temporary_mpq_vector_.emplace_back(value);
  return &temporary_mpq_vector_.back();
}

std::ostream& operator<<(std::ostream& os, const BoundedPolynomialPreprocessor& preprocessor) {
  return os << "BoundCheckerPreprocessor{" << "env_ = " << preprocessor.env() << ", "
            << "var_bounds_ = " << preprocessor.var_bounds() << "}";
}

}  // namespace dlinear
