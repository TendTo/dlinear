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
    : is_consolidated_{false},
      simplex_sat_phase_{config.simplex_sat_phase()},
      precision_{config.precision()},
      needs_expansion_{config.filename_extension() == "smt2"},
      predicate_abstractor_{predicate_abstractor},
      model_{} {}

const std::vector<Variable> &TheorySolver::GetLinearVarMap() const {
  DLINEAR_TRACE("TheorySolver::GetLinearVarMap(): theory_col_to_var_ =");
  if (DLINEAR_TRACE_ENABLED) {
    for (int theory_col = 0; theory_col < static_cast<int>(theory_col_to_var_.size()); theory_col++) {
      const Variable &var{theory_col_to_var_[theory_col]};
      std::cerr << theory_col << ": " << var << "\n";
    }
  }
  return theory_col_to_var_;
}

const Box &TheorySolver::GetModel() const {
  DLINEAR_DEBUG_FMT("TheorySolver::GetModel():\n{}", model_);
  return model_;
}

size_t TheorySolver::n_variables() const { return theory_col_to_var_.size(); }

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

std::vector<LiteralSet> TheorySolver::TheoryBoundsToExplanations(Violation violation, const int theory_col) const {
  std::vector<LiteralSet> explanations{};
  TheoryBoundsToExplanations(violation, theory_col, explanations);
  return explanations;
}
void TheorySolver::TheoryBoundsToExplanations(Violation violation, int theory_bound,
                                              std::vector<LiteralSet> explanations) const {
  const Literal bound_lit{theory_bound_to_lit_[theory_bound]};
  for (; violation; ++violation) {
    explanations.push_back({bound_lit, theory_bound_to_lit_[std::get<2>(*violation)]});
  }
}
void TheorySolver::TheoryBoundsToExplanation(const int theory_col, const bool active, LiteralSet &explanation) const {
  if (active) {
    for (auto it = theory_bounds_[theory_col].active_bounds(); it; ++it)
      explanation.insert(theory_bound_to_lit_[std::get<2>(*it)]);
  } else {
    for (const auto &bound : theory_bounds_[theory_col].bounds()) {
      explanation.insert(theory_bound_to_lit_[std::get<2>(bound)]);
    }
  }
}
void TheorySolver::TheoryBoundsToExplanation(const int theory_col, const mpq_class &value,
                                             LiteralSet &explanation) const {
  for (auto it = theory_bounds_[theory_col].ViolatedBounds(value); it; ++it)
    explanation.insert(theory_bound_to_lit_[std::get<2>(*it)]);
}

void TheorySolver::TheoryBoundsToBoundIdxs(TheorySolver::Violation violation, std::set<int> &bound_idxs) {
  for (; violation; ++violation) bound_idxs.insert(std::get<2>(*violation));
}
void TheorySolver::TheoryBoundsToBoundIdxs(const int theory_col, const bool active, std::set<int> &bound_idxs) const {
  if (active) {
    for (auto it = theory_bounds_[theory_col].active_bounds(); it; ++it) bound_idxs.insert(std::get<2>(*it));
  } else {
    for (const auto &bound : theory_bounds_[theory_col].bounds()) bound_idxs.insert(std::get<2>(bound));
  }
}
void TheorySolver::TheoryBoundsToBoundIdxs(const int theory_col, const mpq_class &value,
                                           std::set<int> &bound_idxs) const {
  for (auto it = theory_bounds_[theory_col].ViolatedBounds(value); it; ++it) bound_idxs.insert(std::get<2>(*it));
}

}  // namespace dlinear
