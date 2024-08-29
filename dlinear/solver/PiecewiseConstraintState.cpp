#include "PiecewiseConstraintState.h"

#include <iostream>

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
    case PiecewiseConstraintState::FIXED:
      os << "FIXED";
      break;
  }
  return os;
}

}  // namespace dlinear