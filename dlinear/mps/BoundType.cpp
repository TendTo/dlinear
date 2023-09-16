/**
 * @file BoundType.cpp
 * @author dlinear
 * @date 16 Sep 2023
 * @copyright 2023 dlinear
 */

#include "BoundType.h"

#include <cstring>

#include "dlinear/util/exception.h"

namespace dlinear::mps {

BoundType ParseBoundType(const std::string& bound_type) { return ParseBoundType(bound_type.c_str()); }

BoundType ParseBoundType(const char bound_type[]) {
  while (*bound_type == ' ') ++bound_type;
  if (!strncasecmp(bound_type, "LO", 2)) return BoundType::LO;
  if (!strncasecmp(bound_type, "LI", 2)) return BoundType::LI;
  if (!strncasecmp(bound_type, "UP", 2)) return BoundType::UP;
  if (!strncasecmp(bound_type, "UI", 2)) return BoundType::UI;
  if (!strncasecmp(bound_type, "FX", 2)) return BoundType::FX;
  if (!strncasecmp(bound_type, "FR", 2)) return BoundType::FR;
  if (!strncasecmp(bound_type, "MI", 2)) return BoundType::MI;
  if (!strncasecmp(bound_type, "PL", 2)) return BoundType::PL;
  if (!strncasecmp(bound_type, "BV", 2)) return BoundType::BV;
  DLINEAR_UNREACHABLE();
}

std::ostream& operator<<(std::ostream& os, const BoundType& bound) {
  switch (bound) {
    case BoundType::LO:
      return os << "LO";
    case BoundType::LI:
      return os << "LI";
    case BoundType::UP:
      return os << "UP";
    case BoundType::UI:
      return os << "UI";
    case BoundType::FX:
      return os << "FX";
    case BoundType::FR:
      return os << "FR";
    case BoundType::MI:
      return os << "MI";
    case BoundType::PL:
      return os << "PL";
    case BoundType::BV:
      return os << "BV";
    default:
      DLINEAR_UNREACHABLE();
  }
}

}  // namespace dlinear::mps
