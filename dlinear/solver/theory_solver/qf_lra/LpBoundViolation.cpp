/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "LpBoundViolation.h"

#include <ostream>

namespace dlinear {

std::ostream &operator<<(std::ostream &os, const LpBoundViolation &violation) {
  return os << "LpBoundViolation{" << violation.column << " (" << (violation.upper_bound_violated ? 'U' : 'L') << ")}";
}

}  // namespace dlinear
