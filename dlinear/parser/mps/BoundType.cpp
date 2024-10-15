/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */

#include "BoundType.h"

#include <iostream>

#include "dlinear/util/exception.h"

namespace dlinear::mps {

BoundType ParseBoundType(const std::string& bound_type) { return ParseBoundType(bound_type.c_str()); }

BoundType ParseBoundType(const char bound_type[]) {
  while (*bound_type == ' ') ++bound_type;
  DLINEAR_ASSERT(strlen(bound_type) == 2, "Bound type must be exactly 2 characters long");
  if (bound_type[2] != '\0' && bound_type[2] != ' ') DLINEAR_RUNTIME_ERROR_FMT("Invalid bound type: '{}'", bound_type);
  if ((bound_type[0] == 'l' || bound_type[0] == 'L') && (bound_type[1] == 'o' || bound_type[1] == 'O')) {
    return BoundType::LO;
  }
  if ((bound_type[0] == 'l' || bound_type[0] == 'L') && (bound_type[1] == 'i' || bound_type[1] == 'I')) {
    return BoundType::LI;
  }
  if ((bound_type[0] == 'u' || bound_type[0] == 'U') && (bound_type[1] == 'p' || bound_type[1] == 'P')) {
    return BoundType::UP;
  }
  if ((bound_type[0] == 'u' || bound_type[0] == 'U') && (bound_type[1] == 'i' || bound_type[1] == 'I')) {
    return BoundType::UI;
  }
  if ((bound_type[0] == 'f' || bound_type[0] == 'F') && (bound_type[1] == 'x' || bound_type[1] == 'X')) {
    return BoundType::FX;
  }
  if ((bound_type[0] == 'f' || bound_type[0] == 'F') && (bound_type[1] == 'r' || bound_type[1] == 'R')) {
    return BoundType::FR;
  }
  if ((bound_type[0] == 'm' || bound_type[0] == 'M') && (bound_type[1] == 'i' || bound_type[1] == 'I')) {
    return BoundType::MI;
  }
  if ((bound_type[0] == 'p' || bound_type[0] == 'P') && (bound_type[1] == 'l' || bound_type[1] == 'L')) {
    return BoundType::PL;
  }
  if ((bound_type[0] == 'b' || bound_type[0] == 'B') && (bound_type[1] == 'v' || bound_type[1] == 'V')) {
    return BoundType::BV;
  }
  DLINEAR_RUNTIME_ERROR_FMT("Invalid bound type: '{}'", bound_type);
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
