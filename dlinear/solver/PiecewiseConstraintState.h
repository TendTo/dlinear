/**
* @file PiecewiseConstraintState.h
* @author dlinear (https://github.com/TendTo/dlinear)
* @copyright 2024 dlinear
* @licence Apache-2.0 license
* PiecewiseConstraintState class
*/
#pragma once

#include <iosfwd>

namespace dlinear {

enum class PiecewiseConstraintState {
  NOT_FIXED,  ///< The constraint is not fixed yet
  INACTIVE,   ///< The constraint is inactive
  ACTIVE,     ///< The constraint is active
};

std::ostream& operator<<(std::ostream& os, const PiecewiseConstraintState& status);

}  // namespace dlinear
