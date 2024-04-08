/**
 * @file ExpressionKind.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @copyright 2019 Drake (https://drake.mit.edu)
 * @licence Apache-2.0 license
 * @brief ExpressionKind enum
 *
 * Kinds of symbolic expressions.
 */
#pragma once

#include <cstdint>
#include <iostream>

namespace dlinear::symbolic {

/**
 * Kinds of symbolic expressions.
 * @internal The constants here are carefully chosen to support nanboxing.
 * For all elements except Constant, the bit pattern must have have 0x7FF0 bits set,
 * but must not be exactly 0x7FF0 nor 0xFFF0 (reserved for ±infinity).
 * Refer to the details in boxed_cell.h for more information.
 */
enum class ExpressionKind : std::uint16_t {
  // clang-format off
  CONSTANT = 0,           ///< constant (double)
  VAR = 0x7FF1u,          ///< variable
  ADD,                    ///< addition (+)
  MUL,                    ///< multiplication (*)
  DIV,                    ///< division (/)
  LOG,                    ///< logarithms
  ABS,                    ///< absolute value function
  EXP,                    ///< exponentiation
  SQRT,                   ///< square root
  POW,                    ///< power function
  SIN,                    ///< sine
  COS,                    ///< cosine
  TAN,                    ///< tangent
  ASIN,                   ///< arcsine
  ACOS,                   ///< arccosine
  ATAN,                   ///< arctangent
  // Here we have Atan = 0x7FFFu, but we can't overflow to 0x8000 for Atan2 so
  // restart numbering at the next available value (0xFFF1).
  ATAN2 = 0xFFF1u,        ///< arctangent2 (atan2(y,x) = atan(y/x))
  SINH,                   ///< hyperbolic sine
  COSH,                   ///< hyperbolic cosine
  TANH,                   ///< hyperbolic tangent
  MIN,                    ///< min
  MAX,                    ///< max
  CEIL,                   ///< ceil
  FLOOR,                  ///< floor
  IF_THEN_ELSE,           ///< if then else
  NAN,                    ///< NaN
  UNINTERPRETED_FUNCTION, ///< Uninterpreted function
  // TODO(soonho): add Integral
  // clang-format on
};

/** Total ordering between ExpressionKinds. */
inline bool operator<(ExpressionKind k1, ExpressionKind k2) {
  return static_cast<std::uint16_t>(k1) < static_cast<std::uint16_t>(k2);
}

std::ostream &operator<<(std::ostream &os, ExpressionKind kind);

}  // namespace dlinear::symbolic
   // namespace drake
