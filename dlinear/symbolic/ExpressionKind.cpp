/**
 * @file ExpressionKind.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @copyright 2019 Drake (https://drake.mit.edu)
 * @licence Apache-2.0 license
 */
#include "ExpressionKind.h"

namespace dlinear::symbolic {

std::ostream &operator<<(std::ostream &os, const ExpressionKind &kind) {
  switch (kind) {
    case ExpressionKind::CONSTANT:
      return os << "CONSTANT";
    case ExpressionKind::VAR:
      return os << "VARIABLE";
    case ExpressionKind::ADD:
      return os << "ADD";
    case ExpressionKind::MUL:
      return os << "MUL";
    case ExpressionKind::DIV:
      return os << "DIV";
    case ExpressionKind::POW:
      return os << "POW";
    case ExpressionKind::SIN:
      return os << "SIN";
    case ExpressionKind::COS:
      return os << "COS";
    case ExpressionKind::TAN:
      return os << "TAN";
    case ExpressionKind::ASIN:
      return os << "ASIN";
    case ExpressionKind::ACOS:
      return os << "ACOS";
    case ExpressionKind::ATAN:
      return os << "ATAN";
    case ExpressionKind::ATAN2:
      return os << "ATAN2";
    case ExpressionKind::SINH:
      return os << "SINH";
    case ExpressionKind::COSH:
      return os << "COSH";
    case ExpressionKind::TANH:
      return os << "TANH";
    case ExpressionKind::LOG:
      return os << "LOG";
    case ExpressionKind::EXP:
      return os << "EXP";
    case ExpressionKind::SQRT:
      return os << "SQRT";
    case ExpressionKind::ABS:
      return os << "ABS";
    case ExpressionKind::FLOOR:
      return os << "FLOOR";
    case ExpressionKind::CEIL:
      return os << "CEIL";
    case ExpressionKind::MIN:
      return os << "MIN";
    case ExpressionKind::MAX:
      return os << "MAX";
    case ExpressionKind::IF_THEN_ELSE:
      return os << "IF_THEN_ELSE";
    case ExpressionKind::NAN:
      return os << "NAN";
    case ExpressionKind::UNINTERPRETED_FUNCTION:
      return os << "UNINTERPRETED_FUNCTION";
  }
}

}  // namespace dlinear::symbolic
