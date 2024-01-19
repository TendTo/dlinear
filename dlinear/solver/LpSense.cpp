//
// Created by c3054737 on 16/01/24.
//

#include "LpSense.h"

#include "dlinear/util/exception.h"

namespace dlinear {

constexpr LpSense parseLpSense(char sense) {
  switch (sense) {
    case 'g':
    case '>':
      return LpSense::GT;
    case 'G':
      return LpSense::GE;
    case '=':
    case 'E':
      return LpSense::EQ;
    case 'N':
      return LpSense::NQ;
    case 'L':
      return LpSense::LE;
    case '<':
    case 'l':
      return LpSense::LT;
    case 'I':
      return LpSense::IN;
    default:
      DLINEAR_UNREACHABLE();
  }
}

constexpr char toChar(LpSense sense) {
  switch (sense) {
    case LpSense::GT:
      return 'g';
    case LpSense::GE:
      return 'G';
    case LpSense::EQ:
      return 'E';
    case LpSense::NQ:
      return 'N';
    case LpSense::LE:
      return 'L';
    case LpSense::LT:
      return 'l';
    case LpSense::IN:
      return 'I';
    default:
      DLINEAR_UNREACHABLE();
  }
}

constexpr LpSense operator!(LpSense sense) {
  switch (sense) {
    case LpSense::GT:
      return LpSense::LE;
    case LpSense::GE:
      return LpSense::LT;
    case LpSense::EQ:
      return LpSense::NQ;
    case LpSense::NQ:
      return LpSense::EQ;
    case LpSense::LE:
      return LpSense::GT;
    case LpSense::LT:
      return LpSense::GE;
    case LpSense::IN:
      return LpSense::IN;
    default:
      DLINEAR_UNREACHABLE();
  }
}

constexpr double epsilon_multiplier(LpSense sense) {
  switch (sense) {
    case LpSense::GT:
      return -1;
    case LpSense::NQ:
    case LpSense::LE:
      return 1;
    default:
      return 0;
  }
}

std::ostream &operator<<(std::ostream &os, const LpSense &lp_result) { return os << toChar(lp_result); }

}  // namespace dlinear
