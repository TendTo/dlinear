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
    : simplex_sat_phase_{config.simplex_sat_phase()},
      precision_{config.precision()},
      needs_expansion_{config.filename_extension() == "smt2"},
      predicate_abstractor_{predicate_abstractor} {}

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

void TheorySolver::AddLiterals(const std::vector<Literal> &theory_literals) {
  for (const auto &lit : theory_literals) AddLiteral(lit);
}

std::optional<LiteralSet> TheorySolver::EnableLiterals(const std::vector<Literal> &theory_literals) {
  for (const Literal &lit : theory_literals) {
    std::optional<LiteralSet> explanation{EnableLiteral(lit)};
    // Check if the literal that was just enabled is conflicting with the current model.
    // If so, return the explanation containing a superset of the conflicting literals
    if (explanation) return explanation;
  }
  return {};
}

bool TheorySolver::IsSimpleBound(const Formula &formula) {
  // Formula must be a relational formula: `lhs <= rhs`, `lhs >= rhs`, `lhs == rhs` or `lhs != rhs`.
  if (!is_relational(formula)) return false;

  // one between lhs and rhs must be a constant and the other must be a variable.
  const Expression &lhs{get_lhs_expression(formula)};
  const Expression &rhs{get_rhs_expression(formula)};
  return ((is_constant(lhs) && is_variable(rhs)) || (is_variable(lhs) && is_constant(rhs)));
}

bool TheorySolver::IsEqualTo(const Formula &formula, bool truth) {
  return truth ? is_equal_to(formula) : is_not_equal_to(formula);
}

bool TheorySolver::IsNotEqualTo(const Formula &formula, bool truth) { return IsEqualTo(formula, !truth); }

bool TheorySolver::IsGreaterThan(const Formula &formula, bool truth) {
  return truth ? is_greater_than(formula) : is_less_than(formula);
}

bool TheorySolver::IsLessThan(const Formula &formula, bool truth) { return IsGreaterThan(formula, !truth); }

bool TheorySolver::IsGreaterThanOrEqualTo(const Formula &formula, bool truth) {
  return truth ? is_greater_than_or_equal_to(formula) : is_less_than_or_equal_to(formula);
}

bool TheorySolver::IsLessThanOrEqualTo(const Formula &formula, bool truth) {
  return IsGreaterThanOrEqualTo(formula, !truth);
}

TheorySolver::Bound TheorySolver::GetBound(const Formula &formula, bool truth) {
  DLINEAR_ASSERT(IsSimpleBound(formula), "Formula must be a simple bound");

  const Expression &lhs{get_lhs_expression(formula)};
  const Expression &rhs{get_rhs_expression(formula)};
  if (IsEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::B, get_constant_value_ref(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::B, get_constant_value_ref(lhs)};
  }
  if (IsGreaterThan(formula, truth) || IsGreaterThanOrEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::L, get_constant_value_ref(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::U, get_constant_value_ref(lhs)};
  }
  if (IsLessThan(formula, truth) || IsLessThanOrEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::U, get_constant_value_ref(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::L, get_constant_value_ref(lhs)};
  }
  if (IsNotEqualTo(formula, truth)) {
    // If delta > 0, we can ignore not-equal bounds on variables, for they will always be satisfied.
    if (is_variable(lhs) && is_constant(rhs)) return {get_variable(lhs), LpColBound::F, get_constant_value_ref(rhs)};
    if (is_constant(lhs) && is_variable(rhs)) return {get_variable(rhs), LpColBound::F, get_constant_value_ref(lhs)};
  }
  DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
}

}  // namespace dlinear
