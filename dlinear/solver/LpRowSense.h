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

#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/logging.h"

namespace dlinear {

/**
 * Sense of a linear programming row describing a constraint.
 * @warning The order of the enum is important and should not be changed.
 * It is used to compare the senses.
 */
enum class LpRowSense {
  LT = 0,  ///< Less than
  LE = 1,  ///< Less than or equal to
  EQ = 2,  ///< Equal to
  GE = 3,  ///< Greater than or equal to
  GT = 4,  ///< Greater than
  NQ = 5,  ///< Not equal to
  IN = 6,  ///< Inactive
};

/**
 * Parse the sense from a formula
 * @pre f is a relational formula
 * @param f formula to parse
 * @return corresponding sense
 */
LpRowSense parseLpSense(const Formula &f);
/**
 * Parse the sense from a character.
 * @param sense character to parse
 * @return corresponding sense
 */
LpRowSense parseLpSense(char sense);
/**
 * Convert the sense to a character.
 * @param sense sense to convert
 * @return corresponding character
 */
char toChar(LpRowSense sense);
/**
 * Invert the sense with delta == 0.
 *
 * More specifically, !LE == GT, !GE == LT, !EQ == NQ, !NQ == EQ, !IN == IN, !GT == LE, !LT == GE.
 * @warning This is not the same as operator-()
 * @param sense sense to invert
 * @return inverted sense
 * @see operator-(LpRowSense)
 */
LpRowSense operator!(LpRowSense sense);
/**
 * Invert the sense with delta > 0.
 *
 * More specifically, -LE == GT, -GE == LE, -EQ == NQ, -NQ == EQ.
 * Any other sense generates an assertion error
 * @warning This is not the same as operator!()
 * @param sense sense to invert
 * @return inverted sense
 * @see operator!(LpRowSense)
 */
LpRowSense operator-(LpRowSense sense);
/**
 * Relax the sense, assuming delta > 0.e
 *
 * More specifically, LT -> LE, GT -> GE.
 * The other senses remain unchanged.
 * @param sense sense to relax
 * @return relaxed sense
 */
LpRowSense operator~(LpRowSense sense);

std::ostream &operator<<(std::ostream &os, const LpRowSense &lp_result);

}  // namespace dlinear

OSTREAM_FORMATTER(dlinear::LpRowSense)
