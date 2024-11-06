/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "SatResult.h"

#include <ostream>

#include "dlinear/util/error.h"

namespace dlinear {

std::ostream &operator<<(std::ostream &os, const SatResult result) {
  switch (result) {
    case SatResult::UNSOLVED:
      return os << "unsolved";
    case SatResult::SAT:
      return os << "sat";
    case SatResult::DELTA_SAT:
      return os << "delta-sat";
    case SatResult::UNSAT:
      return os << "unsat";
    case SatResult::ERROR:
      return os << "error";
    default:
      DLINEAR_UNREACHABLE();
  }
}

SatResult operator~(const SatResult result) {
  switch (result) {
    case SatResult::SAT:
    case SatResult::DELTA_SAT:
      return SatResult::DELTA_SAT;
    default:
      return result;
  }
}

}  // namespace dlinear
