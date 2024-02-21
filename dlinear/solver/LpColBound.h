/**
 * @file LpColBound.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Bound of a linear program variable.
 *
 * This is a simple enum class that describes the bound of a linear program variable.
 * It is used to limit the values it can assume.
 * The bounds are:
 * - U: upper bound
 * - SU: strict upper bound
 * - B: both upper and lower bound are equal (fixed)
 * - D: variable must be different from the bound
 * - L: lower bound
 * - SL: strict lower bound
 * - F: free variable
 *
 * If the bound is strict, it means that the variable cannot assume the bound value.
 * When using delta complete solvers, strict bounds can be relaxed to non-strict bounds.
 */
#pragma once

#include <ostream>

namespace dlinear {

/**
 * Describes the bound of a linear program variable.
 */
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
 *
 * More specifically, !U == SL, !SU == L, !B == D, !D == B, !IN == IN, !L == SU, !SL == U.
 * @warning This is not the same as operator-()
 * @param bound bound to invert
 * @return inverted bound
 */
LpColBound operator!(LpColBound bound);
/**
 * Invert the bound with delta > 0
 *
 * More specifically, -U == L, -L == U, -B == F, -F == B.
 * Any other bound generates an assertion error
 * @warning This is not the same as operator!()
 * @param bound bound to invert
 * @return inverted bound
 */
LpColBound operator-(LpColBound bound);
/**
 * Relax the bound.
 *
 * More specifically, ~SL == L, ~SU == U, ~D == F.
 * Any other bound remain unchanged.
 * @param bound bound to relax
 * @return relaxed bound
 */
LpColBound operator~(LpColBound bound);
/**
 * Relax the bound.
 *
 * More specifically, ~SL == L, ~SU == U, ~D == F.
 * Any other bound remain unchanged.
 * @param bound bound to relax
 * @return relaxed bound
 */
inline LpColBound relax(LpColBound bound) { return ~bound; }
/**
 * Invert the bound.
 *
 * Depending on whether the value of delta is > 0 or not, there are two possible conversion:
 * - If delta > 0: !U == SL, !SU == L, !B == D, !D == B, !IN == IN, !L == SU, !SL == U
 * - If delta == 0: -U == L, -L == U, -B == F, -F == B
 * Any other bound generates an assertion error
 * @note this function combines both ! and - operators
 * @param bound bound to invert
 * @param delta whether delta is greater than 0
 * @return inverted bound
 */
inline LpColBound invert(LpColBound bound, bool delta) { return delta ? -bound : !bound; }

std::ostream &operator<<(std::ostream &os, const LpColBound &bound);

}  // namespace dlinear
