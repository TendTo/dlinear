/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "SatResult.h"

#include "dlinear/util/exception.h"

namespace dlinear {

std::ostream &operator<<(std::ostream &os, const SatResult &logic) {
  switch (logic) {
    case SatResult::SAT_NO_RESULT:
      return os << "no-result";
    case SatResult::SAT_UNSOLVED:
      return os << "unsolved";
    case SatResult::SAT_UNSATISFIABLE:
      return os << "unsat";
    case SatResult::SAT_SATISFIABLE:
      return os << "sat";
    case SatResult::SAT_DELTA_SATISFIABLE:
      return os << "delta-sat";
    default:
      DLINEAR_UNREACHABLE();
  }
}

}  // namespace dlinear
