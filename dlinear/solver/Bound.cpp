/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "Bound.h"

namespace dlinear {

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
