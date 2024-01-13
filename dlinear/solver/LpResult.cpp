//
// Created by c3054737 on 12/01/24.
//

#include "LpResult.h"

#include "dlinear/util/exception.h"

using std::ostream;
using std::string;

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

ostream &operator<<(ostream &os, const LpResult &logic) {
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
