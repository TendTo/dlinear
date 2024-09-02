//
// Created by c3054737 on 28/08/24.
//
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
