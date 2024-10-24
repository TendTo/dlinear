/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * LpRowSense enum.
 */
#pragma once

#include <ostream>

#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

/**
 * Sense of a linear programming row describing a constraint.
 *
 * If the sense is strict, it means that the variable cannot assume the right-hand-side value.
 * When using delta complete solvers, strict senses can be relaxed to non-strict senses.
 * @warning The order of the enum is important and should not be changed.
 * It is used to compare the senses.
 */
enum class LpRowSense {
  LT = 0,  ///< Less than
  EQ = 1,  ///< Equal to
  LE = 2,  ///< Less than or equal to
  GE,      ///< Greater than or equal to
  GT,      ///< Greater than
  NQ,      ///< Not equal to
  IN,      ///< Inactive
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

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::LpRowSense)

#endif
