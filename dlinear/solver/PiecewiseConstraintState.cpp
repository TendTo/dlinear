/**
* @file PiecewiseConstraintState.cpp
* @author dlinear (https://github.com/TendTo/dlinear)
* @copyright 2024 dlinear
* @licence Apache-2.0 license
 */
#include "PiecewiseConstraintState.h"

#include <iostream>

#include "dlinear/util/exception.h"

namespace dlinear {

std::ostream& operator<<(std::ostream& os, const PiecewiseConstraintState& status) {
  switch (status) {
    case PiecewiseConstraintState::NOT_FIXED:
      os << "NOT_FIXED";
      break;
    case PiecewiseConstraintState::INACTIVE:
      os << "INACTIVE";
      break;
    case PiecewiseConstraintState::ACTIVE:
      os << "ACTIVE";
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
  return os;
}

}  // namespace dlinear
