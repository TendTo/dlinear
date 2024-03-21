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

TheorySolver::TheorySolver(const PredicateAbstractor &predicate_abstractor, const Config &config)
    : TheorySolver{"TheorySolver", predicate_abstractor, config} {}
TheorySolver::TheorySolver(const std::string &class_name, const PredicateAbstractor &predicate_abstractor,
                           const Config &config)
    : is_consolidated_{false},
      simplex_sat_phase_{config.simplex_sat_phase()},
      precision_{config.precision()},
      needs_expansion_{config.filename_extension() == "smt2"},
      predicate_abstractor_{predicate_abstractor},
      model_{},
      stats_{DLINEAR_INFO_ENABLED, class_name, "Total time spent in CheckSat", "Total # of CheckSat"} {}

const Box &TheorySolver::GetModel() const {
  DLINEAR_DEBUG_FMT("TheorySolver::GetModel():\n{}", model_);
  return model_;
}

void TheorySolver::AddLiterals(const std::vector<Literal> &theory_literals) {
  for (const auto &lit : theory_literals) AddLiteral(lit);
}

std::vector<LiteralSet> TheorySolver::EnableLiterals(const std::vector<Literal> &theory_literals) {
  std::vector<LiteralSet> explanations{};
  for (const Literal &lit : theory_literals) {
    std::vector<LiteralSet> explanation{EnableLiteral(lit)};
    explanations.insert(explanations.end(), explanation.begin(), explanation.end());
    // Check if the literal that was just enabled is conflicting with the current model.
    // If so, return the explanation containing a superset of the conflicting literals
  }
  return explanations;
}

void TheorySolver::Consolidate() {
  if (is_consolidated_) return;
  DLINEAR_DEBUG("TheorySolver::Consolidate()");
  is_consolidated_ = true;
}

bool TheorySolver::IsSimpleBound(const Formula &formula) {
  // Formula must be a relational formula: `lhs <= rhs`, `lhs >= rhs`, `lhs == rhs` or `lhs != rhs`.
  if (!is_relational(formula)) return false;

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
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::B, get_constant_value_ref(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::B, get_constant_value_ref(lhs)};
  }
  if (IsGreaterThan(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::SL, get_constant_value_ref(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::SU, get_constant_value_ref(lhs)};
  }
  if (IsGreaterThanOrEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::L, get_constant_value_ref(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::U, get_constant_value_ref(lhs)};
  }
  if (IsLessThan(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::SU, get_constant_value_ref(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::SL, get_constant_value_ref(lhs)};
  }
  if (IsLessThanOrEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::U, get_constant_value_ref(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::L, get_constant_value_ref(lhs)};
  }
  if (IsNotEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::D, get_constant_value_ref(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::D, get_constant_value_ref(lhs)};
  }
  DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
}

std::vector<LiteralSet> TheorySolver::TheoryBoundsToExplanations(Violation violation, const int theory_row) const {
  std::vector<LiteralSet> explanations{};
  TheoryBoundsToExplanations(violation, theory_row, explanations);
  return explanations;
}
void TheorySolver::TheoryBoundsToExplanations(Violation violation, int theory_row,
                                              std::vector<LiteralSet> &explanations) const {
  const Literal row_lit{theory_row_to_lit_[theory_row]};
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::TheoryBoundsToExplanations: {} violates {}", row_lit, violation);
  if (violation.nq_bounds_empty() || violation.bounds_empty()) {
    for (; violation; ++violation) explanations.push_back({row_lit, theory_row_to_lit_[std::get<2>(*violation)]});
  } else {
    explanations.emplace_back();
    for (; violation; ++violation) explanations.back().insert(theory_row_to_lit_[std::get<2>(*violation)]);
  }
}
void TheorySolver::TheoryBoundsToExplanation(const int theory_col, const bool active, LiteralSet &explanation) const {
  if (active) {
    theory_bounds_.at(theory_col).GetActiveExplanation(theory_row_to_lit_, explanation);
  } else {
    for (const auto &bound : theory_bounds_[theory_col].bounds()) {
      explanation.insert(theory_row_to_lit_[std::get<2>(bound)]);
    }
  }
}

void TheorySolver::TheoryBoundsToBoundIdxs(TheorySolver::Violation violation, std::set<int> &bound_idxs) {
  for (; violation; ++violation) bound_idxs.insert(std::get<2>(*violation));
}
void TheorySolver::TheoryBoundsToBoundIdxs(const int theory_col, const bool active, std::set<int> &bound_idxs) const {
  if (active) {
    for (auto it = theory_bounds_[theory_col].GetActiveBounds(); it; ++it) bound_idxs.insert(std::get<2>(*it));
  } else {
    for (const auto &bound : theory_bounds_[theory_col].bounds()) bound_idxs.insert(std::get<2>(bound));
  }
}

}  // namespace dlinear
