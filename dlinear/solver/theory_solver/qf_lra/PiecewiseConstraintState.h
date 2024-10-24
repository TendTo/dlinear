/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * PiecewiseConstraintState enum.
 */
#pragma once

#include <iosfwd>

namespace dlinear {

/** State a piecewise constraint can be in */
enum class PiecewiseConstraintState {
  NOT_FIXED,  ///< The constraint is not fixed yet
  INACTIVE,   ///< The constraint is inactive
  ACTIVE,     ///< The constraint is active
};

std::ostream& operator<<(std::ostream& os, const PiecewiseConstraintState& status);

}  // namespace dlinear
