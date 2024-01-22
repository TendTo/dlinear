//
// Created by c3054737 on 16/01/24.
//
#pragma once

#include <ostream>

namespace dlinear {

enum class LpRowSense {
  GT,  ///< Greater than
  GE,  ///< Greater than or equal to
  EQ,  ///< Equal to
  NQ,  ///< Not equal to
  LE,  ///< Less than or equal to
  LT,  ///< Less than
  IN,  ///< Inactive
};

LpRowSense parseLpSense(char sense);
char toChar(LpRowSense sense);
/**
 * Invert the sense with delta == 0
 * @note This is not the same as operator!()
 * More specifically, !LE == GT, !GE == LT, !EQ == NQ, !NQ == EQ, !IN == IN, !GT == LE, !LT == GE.
 * @param sense
 * @return
 */
LpRowSense operator!(LpRowSense sense);
/**
 * Invert the sense with delta > 0
 * @note This is not the same as operator!()
 * More specifically, ~LE == GT, ~GE == LE, ~EQ == NQ, ~NQ == EQ.
 * Any other sense generates an assertion error
 * @param sense sense to invert
 * @return inverted sense
 */
LpRowSense operator~(LpRowSense sense);
double epsilon_multiplier(LpRowSense sense);
std::ostream &operator<<(std::ostream &os, const LpRowSense &lp_result);

}  // namespace dlinear
