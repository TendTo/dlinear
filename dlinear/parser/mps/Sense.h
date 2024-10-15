/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Sense of a constraint row.
 *
 * The sense indicates the type or relation a contraint row has with
 * respect to its right-hand side.
 * The supported values are 'L', 'E', 'G', or 'N'.
 * They represent, respectively, less than, equal to, greater than, or
 * no constraint, usually applied to the objective function.
 */
#pragma once

#include <iosfwd>
#include <string>

namespace dlinear::mps {

/**
 * Sense of a constraint row.
 */
enum class Sense {
  L,  ///< Less or equal to
  E,  ///< Equal to
  G,  ///< Greater or equal to
  N   ///< No sense, used for the objective function
};

/**
 * Parse a sense from a string.
 * The string must be one of the following:
 * - "L"
 * - "E"
 * - "G"
 * - "N"
 *
 * Any leading or trailing spaces are ignored.
 * The input is case-insensitive.
 * @param sense string representation of the sense
 * @return corresponding sense
 */
Sense ParseSense(const std::string &sense);
/**
 * Parse a sense from a C-style string.
 * The string must be one of the following:
 * - "L"
 * - "E"
 * - "G"
 * - "N"
 *
 * Any leading or trailing spaces are ignored.
 * The input is case-insensitive.
 * @param sense C-style string representation of the sense
 * @return corresponding sense
 */
Sense ParseSense(const char sense[]);
/**
 * Parse a sense from a character.
 * The character must be one of the following:
 * - 'L'
 * - 'E'
 * - 'G'
 * - 'N'
 *
 * The input is case-insensitive.
 * @param sense character representation of the sense
 * @return corresponding sense
 */
Sense ParseSense(char sense);

std::ostream &operator<<(std::ostream &os, const Sense &sense);

}  // namespace dlinear::mps

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::mps::Sense)

#endif
