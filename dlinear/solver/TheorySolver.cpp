/**
 * @file TheorySolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "TheorySolver.h"

#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

TheorySolver::TheorySolver(const PredicateAbstractor &predicate_abstractor, const std::string &class_name)
    : config_{predicate_abstractor.config()},
      is_consolidated_{false},
      predicate_abstractor_{predicate_abstractor},
      fixed_preprocessor_{predicate_abstractor},
      preprocessor_{predicate_abstractor},
      model_{config_.lp_solver()},
      stats_{config_.with_timings(), class_name, "Total time spent in CheckSat", "Total # of CheckSat"} {}

const Box &TheorySolver::model() const {
  DLINEAR_DEBUG_FMT("TheorySolver::model():\n{}", model_);
  return model_;
}

void TheorySolver::AddLiterals() {
  for (const auto &[var, f] : predicate_abstractor_.var_to_formula_map()) AddLiteral(var, f);
}

TheorySolver::Explanations TheorySolver::AddFixedLiterals(const LiteralSet &fixed_literals) {
  Explanations explanations{};
  for (const Literal &lit : fixed_literals) fixed_preprocessor_.EnableLiteral(lit, explanations);
  fixed_preprocessor_.Process(explanations);
  return explanations;
}

TheorySolver::Explanations TheorySolver::EnableLiterals(const std::vector<Literal> &theory_literals) {
  Explanations explanations{};
  for (const Literal &lit : theory_literals) {
    const Explanations explanation{EnableLiteral(lit)};
    // Check if the literal that was just enabled is conflicting with the current model.
    // If so, return the explanation containing a superset of the conflicting literals
    explanations.insert(explanation.begin(), explanation.end());
  }
  return explanations;
}

void TheorySolver::UpdateExplanations(Explanations &explanations) {
  DLINEAR_TRACE("TheorySolver::UpdateExplanation()");
  LiteralSet explanation{};
  UpdateExplanation(explanation);
  explanations.insert(explanation);
}

void TheorySolver::Consolidate() {
  if (is_consolidated_) return;
  DLINEAR_DEBUG("TheorySolver::Consolidate()");
  is_consolidated_ = true;
  enabled_theory_rows_.reserve(theory_row_to_lit_.size());
  theory_rows_state_.resize(theory_row_to_lit_.size(), false);
}
#if 0
bool TheorySolver::IsSimpleBound(const Formula &formula) {
  // Formula must be a relational formula: `lhs <= rhs`, `lhs >= rhs`, `lhs == rhs` or `lhs != rhs`.
  if (!is_relational(formula)) return false;
  // The number of variables must be exactly one
  if (formula.GetFreeVariables().size() != 1) return false;

  // one between lhs and rhs must be a constant and the other must be a variable.
  const Expression &lhs{get_lhs_expression(formula)};
  const Expression &rhs{get_rhs_expression(formula)};
  return ((is_constant(lhs) && is_variable(rhs)) || (is_variable(lhs) && is_constant(rhs)));
}

bool TheorySolver::IsEqualTo(const Formula &formula, const bool truth) {
  return truth ? is_equal_to(formula) : is_not_equal_to(formula);
}

bool TheorySolver::IsNotEqualTo(const Formula &formula, const bool truth) {
  return truth ? is_not_equal_to(formula) : is_equal_to(formula);
}

bool TheorySolver::IsGreaterThan(const Formula &formula, const bool truth) {
  return truth ? is_greater_than(formula) : is_less_than_or_equal_to(formula);
}

bool TheorySolver::IsLessThan(const Formula &formula, const bool truth) {
  return truth ? is_less_than(formula) : is_greater_than_or_equal_to(formula);
}

bool TheorySolver::IsGreaterThanOrEqualTo(const Formula &formula, const bool truth) {
  return truth ? is_greater_than_or_equal_to(formula) : is_less_than(formula);
}

bool TheorySolver::IsLessThanOrEqualTo(const Formula &formula, const bool truth) {
  return truth ? is_less_than_or_equal_to(formula) : is_greater_than(formula);
}

TheorySolver::Bound TheorySolver::GetBound(const Formula &formula, const bool truth) {
  DLINEAR_ASSERT(IsSimpleBound(formula), "Formula must be a simple bound");
  const Expression &lhs{get_lhs_expression(formula)};
  const Expression &rhs{get_rhs_expression(formula)};
  if (IsEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::B, get_constant_value(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::B, get_constant_value(lhs)};
  }
  if (IsGreaterThan(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::SL, get_constant_value(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::SU, get_constant_value(lhs)};
  }
  if (IsGreaterThanOrEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::L, get_constant_value(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::U, get_constant_value(lhs)};
  }
  if (IsLessThan(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::SU, get_constant_value(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::SL, get_constant_value(lhs)};
  }
  if (IsLessThanOrEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::U, get_constant_value(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::L, get_constant_value(lhs)};
  }
  if (IsNotEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::D, get_constant_value(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::D, get_constant_value(lhs)};
  }
  DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
}

TheorySolver::Explanations TheorySolver::TheoryBoundsToExplanations(Violation violation, const int theory_row) const {
  Explanations explanations{};
  TheoryBoundsToExplanations(violation, theory_row, explanations);
  return explanations;
}
void TheorySolver::TheoryBoundsToExplanations(Violation violation, int theory_row, Explanations &explanations) const {
  const Literal row_lit{theory_row_to_lit_[theory_row]};
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::TheoryBoundsToExplanations: {} violates {}", row_lit, violation);
  if (violation.nq_bounds_empty() || violation.bounds_empty()) {
    for (; violation; ++violation) explanations.insert({row_lit, theory_row_to_lit_[violation->idx]});
  } else {
    LiteralSet explanation{};
    for (; violation; ++violation) explanation.insert(theory_row_to_lit_[violation->idx]);
    explanations.insert(explanation);
  }
}
void TheorySolver::TheoryBoundsToExplanation(const int theory_col, LiteralSet &explanation) {
  if (!config_.disable_theory_preprocessor() && preprocessor_.env().contains(theory_col_to_var_[theory_col])) {
    preprocessor_.GetActiveExplanation(theory_col, explanation);
  } else {
    theory_bounds_.at(theory_col).GetActiveExplanation(theory_row_to_lit_, explanation);
  }
}
void TheorySolver::TheoryBoundsToExplanation(const int theory_col, const mpq_class &value,
                                             LiteralSet &explanation) const {
  for (auto it = theory_bounds_[theory_col].GetActiveBound(value); it; ++it) {
    explanation.insert(theory_row_to_lit_[it->idx]);
  }
}
void TheorySolver::TheoryBoundsToExplanation(const int theory_col, const TheorySolver::BoundViolationType type,
                                             LiteralSet &explanation) const {
  if (type == BoundViolationType::NO_BOUND_VIOLATION) return;
  const TheorySolverBoundVector &bound = theory_bounds_[theory_col];
  return TheoryBoundsToExplanation(
      theory_col,
      type == BoundViolationType::LOWER_BOUND_VIOLATION ? bound.active_lower_bound() : bound.active_upper_bound(),
      explanation);
}

void TheorySolver::TheoryBoundsToBoundIdxs(TheorySolver::Violation violation, std::set<int> &bound_idxs) {
  for (; violation; ++violation) bound_idxs.insert(violation->idx);
}
void TheorySolver::TheoryBoundsToBoundIdxs(const int theory_col, const bool active, std::set<int> &bound_idxs) const {
  if (active) {
    for (auto it = theory_bounds_[theory_col].GetActiveBound(); it; ++it) bound_idxs.insert(it->idx);
  } else {
    for (const auto &bound : theory_bounds_[theory_col].bounds()) bound_idxs.insert(bound.idx);
  }
}
void TheorySolver::TheoryBoundsToBoundIdxs(const int theory_col, const mpq_class &value,
                                           std::set<int> &bound_idxs) const {
  for (auto it = theory_bounds_[theory_col].GetActiveBound(value); it; ++it) bound_idxs.insert(it->idx);
}
void TheorySolver::TheoryBoundsToBoundIdxs(int theory_col, const TheorySolver::BoundViolationType type,
                                           std::set<int> &bound_idxs) {
  if (type == BoundViolationType::NO_BOUND_VIOLATION) return;
  const TheorySolverBoundVector &bound = theory_bounds_[theory_col];
  if (!config_.disable_theory_preprocessor() && preprocessor_.env().contains(theory_col_to_var_[theory_col])) {
    return preprocessor_.GetActiveBoundIdxs(theory_col, bound_idxs);
  }
  return TheoryBoundsToBoundIdxs(
      theory_col,
      type == BoundViolationType::LOWER_BOUND_VIOLATION ? bound.active_lower_bound() : bound.active_upper_bound(),
      bound_idxs);
}
#endif

void TheorySolver::BoundsToTheoryRows(const Variable &var, BoundViolationType type, std::set<int> &theory_rows) const {
  if (type == BoundViolationType::NO_BOUND_VIOLATION) return;
  auto it = preprocessor_.theory_bounds().find(var);
  if (it == preprocessor_.theory_bounds().end()) return;
  const BoundVector &bound = it->second;
  return BoundsToTheoryRows(
      var, type == BoundViolationType::LOWER_BOUND_VIOLATION ? bound.active_lower_bound() : bound.active_upper_bound(),
      theory_rows);
}
void TheorySolver::BoundsToTheoryRows(const Variable &var, const mpq_class &value, std::set<int> &theory_rows) const {
  auto bound_it = preprocessor_.theory_bounds().find(var);
  if (bound_it == preprocessor_.theory_bounds().end()) return;
  const BoundVector &bound = bound_it->second;
  for (auto it = bound.GetActiveBound(value); it; ++it) {
    theory_rows.insert(lit_to_theory_row_.at(it->theory_literal.var.get_id()));
    for (const Literal &exp : it->explanation) theory_rows.insert(lit_to_theory_row_.at(exp.var.get_id()));
  }
}

}  // namespace dlinear
