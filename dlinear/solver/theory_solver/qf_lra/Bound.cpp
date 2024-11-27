/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "Bound.h"

#include <ostream>

#include "dlinear/util/error.h"

namespace dlinear {

Bound Bound::Parse(const Literal& lit, const Formula& formula) {
  DLINEAR_ASSERT_FMT(IsSimpleBound(formula), "Expected simple bound, got {}", formula);
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

std::strong_ordering Bound::operator<=>(const Bound& other) const {
  const auto& [value_l, type_l, lit_l, expl_l] = *this;
  const auto& [value_r, type_r, lit_r, expl_r] = other;
  if (*value_l < *value_r) return std::strong_ordering::less;
  if (*value_l > *value_r) return std::strong_ordering::greater;
  if (type_l < type_r) return std::strong_ordering::less;
  if (type_l > type_r) return std::strong_ordering::greater;
  return std::strong_ordering::equal;
}
bool Bound::operator==(const Bound& other) const {
  const auto& [value_l, type_l, lit_l, expl_l] = *this;
  const auto& [value_r, type_r, lit_r, expl_r] = other;
  return *value_l == *value_r && type_l == type_r && lit_l == lit_r && expl_l == expl_r;
}

std::ostream& operator<<(std::ostream& os, const Bound& bound) {
  const auto& [value, type, lit, expl] = bound;
  return os << "Bound{ " << *value << ", " << type << ", " << lit << ", " << expl << " }";
}

}  // namespace dlinear
