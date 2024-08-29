//
// Created by c3054737 on 28/08/24.
//
#pragma once

#include <iosfwd>

namespace dlinear {

enum class PiecewiseConstraintState {
  NOT_FIXED,
  INACTIVE,
  ACTIVE,
  FIXED,
};

std::ostream& operator<<(std::ostream& os, const PiecewiseConstraintState& status);

}  // namespace dlinear
