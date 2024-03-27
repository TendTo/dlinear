/**
 * @file LinearFormulaFlattener.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "LinearFormulaFlattener.h"

namespace dlinear {

const Formula& LinearFormulaFlattener::Flatten(const Formula& formula) {
  if (!is_relational(formula)) return formula;
  const Expression& lhs = get_lhs_expression(formula);
  const Expression& rhs = get_rhs_expression(formula);
  const Expression expr{needs_expansion_ ? (lhs - rhs).Expand() : lhs - rhs};
  DLINEAR_ASSERT(expr.EqualTo(expr.Expand()), "Expression must be expanded");
  DLINEAR_ASSERT_FMT(is_addition(expr) || is_multiplication(expr) || is_variable(expr),
                     "Expression must be an addition, multiplication or a variable. Instead found {}", expr);

  if (is_addition(expr)) {
    const mpq_class& constant{get_constant_in_addition(expr)};
    if (!needs_expansion_ && expr.EqualTo(lhs) && constant == 0) return formula;
    BuildFlatteredFormula(expr - constant, Expression{-constant}, formula.get_kind());
  } else {
    if (!needs_expansion_ && expr.EqualTo(lhs)) return formula;
    BuildFlatteredFormula(expr, 0, formula.get_kind());
  }

  return flattered_formula_;
}

void LinearFormulaFlattener::BuildFlatteredFormula(const Expression& lhs, const Expression& rhs, FormulaKind kind) {
  switch (kind) {
    case FormulaKind::Eq:
      flattered_formula_ = lhs == rhs;
      break;
    case FormulaKind::Neq:
      flattered_formula_ = lhs != rhs;
      break;
    case FormulaKind::Leq:
      flattered_formula_ = lhs <= rhs;
      break;
    case FormulaKind::Lt:
      flattered_formula_ = lhs < rhs;
      break;
    case FormulaKind::Geq:
      flattered_formula_ = lhs >= rhs;
      break;
    case FormulaKind::Gt:
      flattered_formula_ = lhs > rhs;
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
}

}  // namespace dlinear
