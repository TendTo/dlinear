/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
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
