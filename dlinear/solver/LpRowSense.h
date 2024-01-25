/**
 * @file LpRowSense.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Sense of a linear programming row.
 *
 * This is a simple enum class that describes the sense of a linear programming row.
 * Each row can have one of the following senses:
 * - GT: Greater than (>)
 * - GE: Greater than or equal to (>=)
 * - EQ: Equal to (=)
 * - NQ: Not equal to (!=)
 * - LE: Less than or equal to (<=)
 * - LT: Less than (<)
 * - IN: Inactive (not used)
 *
 * If the sense is strict, it means that the variable cannot assume the right-hand-side value.
 * When using delta complete solvers, strict senses can be relaxed to non-strict senses.
 */
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
