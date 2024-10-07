/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "LpResult.h"

#include "dlinear/util/exception.h"

namespace dlinear {

LpResult parseLogic(const int res) {
  switch (res) {
    case 0:
      return LpResult::LP_UNSOLVED;
    case 1:
      return LpResult::LP_INFEASIBLE;
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::ostream &operator<<(std::ostream &os, const LpResult &logic) {
  switch (logic) {
    case LpResult::LP_NO_RESULT:
      return os << "no-result";
    case LpResult::LP_UNSOLVED:
      return os << "unsolved";
    case LpResult::LP_INFEASIBLE:
      return os << "infeasible";
    case LpResult::LP_UNBOUNDED:
      return os << "unbounded";
    case LpResult::LP_OPTIMAL:
      return os << "optimal";
    case LpResult::LP_DELTA_OPTIMAL:
      return os << "delta-optimal";
    default:
      DLINEAR_UNREACHABLE();
  }
}

}  // namespace dlinear
