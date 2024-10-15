/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Bound type.
 *
 * The bound type is used to specify the type of a variable bound.
 * It is indicated in the MPS file format.
 * The supported values are 'LO', 'LI', 'UP', 'UI', 'FX', 'FR', 'MI', 'PL', or 'BV'.
 * They represent, respectively, lower bound, lower bound integer, upper bound, upper bound integer,
 * fixed bound (lower and upper bound are equal), free bound (lower and upper
 * bound are -/+ infinity), minus infinity (lower bound is -infinity), plus
 * infinity (upper bound is +infinity), or binary variable (either 0 or 1).
 */
#pragma once

#include <iosfwd>
#include <string>

namespace dlinear::mps {

/**
 * Bound type.
 * The bound type is used to specify the type of a variable bound.
 * The bound type is used in the MPS file format.
 */
enum class BoundType {
  LO,  // Lower bound
  LI,  // Lower bound integer
  UP,  // Upper bound
  UI,  // Upper bound integer
  FX,  // Fixed bound (lower and upper bound are equal)
  FR,  // Free bound (lower and upper bound are -/+ infinity)
  MI,  // Minus infinity (lower bound is -infinity)
  PL,  // Plus infinity (upper bound is +infinity)
  BV,  // Binary variable (either 0 or 1)
};

/**
 * Parse a bound type from a string.
 * The string must be one of the following:
 * - "LO"
 * - "LI"
 * - "UP"
 * - "UI"
 * - "FX"
 * - "FR"
 * - "MI"
 * - "PL"
 * - "BV"
 *
 * Any leading or trailing spaces are ignored.
 * The input is case-insensitive.
 *
 * @param bound_type string representation of the bound type
 * @return corresponding bound type
 */
BoundType ParseBoundType(const std::string &bound_type);
/**
 * Parse a bound type from a C-string.
 * The string must be one of the following:
 * - "LO"
 * - "LI"
 * - "UP"
 * - "UI"
 * - "FX"
 * - "FR"
 * - "MI"
 * - "PL"
 * - "BV
 *
 * Any leading or trailing spaces are ignored.
 * The input is case-insensitive.
 * @pre The input must be exactly 2 characters long.
 * @param bound_type C-string representation of the bound type
 * @return corresponding bound type
 */
BoundType ParseBoundType(const char bound_type[]);

std::ostream &operator<<(std::ostream &os, const BoundType &bound);

}  // namespace dlinear::mps

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::mps::BoundType)

#endif
