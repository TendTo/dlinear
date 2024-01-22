//
// Created by c3054737 on 16/01/24.
//
#pragma once

#include <ostream>

namespace dlinear {

enum class LpColBound {
  U,   ///< Upper bound
  SU,  ///< Strict upper bound
  B,   ///< Both upper and lower bound are equal (fixed)
  D,   ///< Variable must be different from the bound
  L,   ///< Lower bound
  SL,  ///< Strict lower bound
  F,   ///< Free variable
};

LpColBound parseLpBound(char bound);
char toChar(LpColBound bound);
/**
 * Invert the bound with delta == 0
 * @note This is not the same as operator!()
 * More specifically, !U == SL, !SU == L, !B == D, !D == B, !IN == IN, !L == SU, !SL == U.
 * @param bound
 * @return
 */
LpColBound operator!(LpColBound bound);
/**
 * Invert the bound with delta > 0
 * @note This is not the same as operator!()
 * More specifically, ~U == L, ~L == U, ~B == F, ~F == B.
 * Any other bound generates an assertion error
 * @param bound bound to invert
 * @return inverted bound
 */
LpColBound operator~(LpColBound bound);
std::ostream &operator<<(std::ostream &os, const LpColBound &bound);

}  // namespace dlinear
