/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "LpColBound.h"

#include "dlinear/util/exception.h"

namespace dlinear {

LpColBound parseLpbound(char bound) {
  switch (bound) {
    case 'u':
      return LpColBound::SU;
    case 'U':
      return LpColBound::U;
    case 'B':
      return LpColBound::B;
    case 'D':
      return LpColBound::D;
    case 'l':
      return LpColBound::SL;
    case 'L':
      return LpColBound::L;
    case 'F':
      return LpColBound::F;
    default:
      DLINEAR_UNREACHABLE();
  }
}

char toChar(LpColBound bound) {
  switch (bound) {
    case LpColBound::SU:
      return 'u';
    case LpColBound::U:
      return 'U';
    case LpColBound::B:
      return 'B';
    case LpColBound::D:
      return 'D';
    case LpColBound::SL:
      return 'l';
    case LpColBound::L:
      return 'L';
    case LpColBound::F:
      return 'F';
    default:
      DLINEAR_UNREACHABLE();
  }
}

LpColBound operator!(LpColBound bound) {
  switch (bound) {
    case LpColBound::SU:
      return LpColBound::L;
    case LpColBound::U:
      return LpColBound::SL;
    case LpColBound::B:
      return LpColBound::D;
    case LpColBound::D:
      return LpColBound::B;
    case LpColBound::SL:
      return LpColBound::U;
    case LpColBound::L:
      return LpColBound::SU;
    default:
      DLINEAR_UNREACHABLE();
  }
}

LpColBound operator-(LpColBound bound) {
  switch (bound) {
    case LpColBound::U:
      return LpColBound::L;
    case LpColBound::L:
      return LpColBound::U;
    case LpColBound::B:
      return LpColBound::F;
    case LpColBound::F:
      return LpColBound::B;
    default:
      DLINEAR_UNREACHABLE();
  }
}

LpColBound operator~(LpColBound bound) {
  switch (bound) {
    case LpColBound::SL:
      return LpColBound::L;
    case LpColBound::SU:
      return LpColBound::U;
    case LpColBound::D:
      return LpColBound::F;
    default:
      return bound;
  }
}

std::ostream &operator<<(std::ostream &os, const LpColBound &bound) { return os << toChar(bound); }

}  // namespace dlinear
