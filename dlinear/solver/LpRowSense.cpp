/**
 * @file LpRowSense.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "LpRowSense.h"

#include "dlinear/util/exception.h"

namespace dlinear {

LpRowSense parseLpSense(char sense) {
  switch (sense) {
    case 'g':
    case '>':
      return LpRowSense::GT;
    case 'G':
      return LpRowSense::GE;
    case '=':
    case 'E':
      return LpRowSense::EQ;
    case 'N':
      return LpRowSense::NQ;
    case 'L':
      return LpRowSense::LE;
    case '<':
    case 'l':
      return LpRowSense::LT;
    case 'I':
      return LpRowSense::IN;
    default:
      DLINEAR_UNREACHABLE();
  }
}

char toChar(LpRowSense sense) {
  switch (sense) {
    case LpRowSense::GT:
      return 'g';
    case LpRowSense::GE:
      return 'G';
    case LpRowSense::EQ:
      return 'E';
    case LpRowSense::NQ:
      return 'N';
    case LpRowSense::LE:
      return 'L';
    case LpRowSense::LT:
      return 'l';
    case LpRowSense::IN:
      return 'I';
    default:
      DLINEAR_UNREACHABLE();
  }
}

LpRowSense operator!(LpRowSense sense) {
  switch (sense) {
    case LpRowSense::GT:
      return LpRowSense::LE;
    case LpRowSense::GE:
      return LpRowSense::LT;
    case LpRowSense::EQ:
      return LpRowSense::NQ;
    case LpRowSense::NQ:
      return LpRowSense::EQ;
    case LpRowSense::LE:
      return LpRowSense::GT;
    case LpRowSense::LT:
      return LpRowSense::GE;
    case LpRowSense::IN:
      return LpRowSense::IN;
    default:
      DLINEAR_UNREACHABLE();
  }
}

LpRowSense operator~(LpRowSense sense) {
  switch (sense) {
    case LpRowSense::GE:
      return LpRowSense::LE;
    case LpRowSense::EQ:
      return LpRowSense::NQ;
    case LpRowSense::LE:
      return LpRowSense::GE;
    case LpRowSense::IN:
      return LpRowSense::IN;
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::ostream &operator<<(std::ostream &os, const LpRowSense &lp_result) { return os << toChar(lp_result); }

}  // namespace dlinear
