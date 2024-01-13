//
// Created by c3054737 on 11/01/24.
//

#include "TheorySolver.h"

#include "dlinear/util/logging.h"

namespace dlinear {

TheorySolver::TheorySolver([[maybe_unused]] const Config &config) : simplex_sat_phase_{config.simplex_sat_phase()} {}

void TheorySolver::AddFormula([[maybe_unused]] const Formula &f) {}

const std::map<int, Variable> &TheorySolver::GetLinearVarMap() const {
  DLINEAR_TRACE("TheorySolver::GetLinearVarMap(): theory_col_to_var_ =");
  if (DLINEAR_TRACE_ENABLED) {
    for (const auto &[theory_idx, var] : theory_col_to_var_) {
      std::cerr << theory_idx << ": " << var << "\n";
    }
  }
  return theory_col_to_var_;
}

const Box &TheorySolver::GetModel() const {
  DLINEAR_DEBUG_FMT("TheorySolver::GetModel():\n{}", model_);
  return model_;
}

void TheorySolver::EnableTheoryLiterals(const std::vector<Literal> &theory_literals,
                                        const VarToTheoryLiteralMap &var_to_theory_literals) {
  for (const Literal &lit : theory_literals) EnableTheoryLiteral(lit, var_to_theory_literals);
}

bool TheorySolver::IsSimpleBound(const Formula &formula) {
  // Formula must be a relational formula: `lhs <= rhs`, `lhs >= rhs`, `lhs == rhs` or `lhs != rhs`.
  if (!is_relational(formula)) return false;

  // one between lhs and rhs must be a constant and the other must be a variable.
  const Expression &lhs{get_lhs_expression(formula)};
  const Expression &rhs{get_rhs_expression(formula)};
  return ((is_constant(lhs) && is_variable(rhs)) || (is_variable(lhs) && is_constant(rhs)));
}

bool TheorySolver::IsEqualToOrWhatever(const Formula &formula, bool truth) {
  return truth ? is_equal_to(formula) : is_not_equal_to(formula);
}

bool TheorySolver::IsNotEqualToOrWhatever(const Formula &formula, bool truth) {
  return IsEqualToOrWhatever(formula, !truth);
}

bool TheorySolver::IsGreaterThanOrWhatever(const Formula &formula, bool truth) {
  return truth ? is_greater_than(formula) || is_greater_than_or_equal_to(formula)
               : is_less_than(formula) || is_less_than_or_equal_to(formula);
}

bool TheorySolver::IsLessThanOrWhatever(const Formula &formula, bool truth) {
  return IsGreaterThanOrWhatever(formula, !truth);
}

}  // namespace dlinear