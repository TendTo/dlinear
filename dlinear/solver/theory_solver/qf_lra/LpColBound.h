/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * LpColBound enum.
 */
#pragma once

#include <ostream>

namespace dlinear {

/**
 * Describe the bound of a linear program variable.
 *
 * If the bound is strict, it means that the variable cannot assume the bound value.
 * When using delta complete solvers, strict bounds can be relaxed to non-strict bounds.
 * @warning The order of the enum is important and should not be changed.
 * It is used to compare the bounds.
 */
enum class LpColBound {
  L = 0,   ///< Lower bound
  SL = 1,  ///< Strict lower bound
  B = 2,   ///< Both upper and lower bound are equal (fixed)
  SU = 3,  ///< Strict upper bound
  U = 4,   ///< Upper bound
  D = 5,   ///< Variable must be different from the bound
  F = 6,   ///< Free variable
};

/**
 * Parse the bound from a character.
 * @param bound character to parse
 * @return corresponding bound
 */
LpColBound parseLpBound(char bound);
/**
 * Convert the bound to a character.
 * @param bound bound to convert
 * @return corresponding character
 */
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

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::LpColBound)

#endif
