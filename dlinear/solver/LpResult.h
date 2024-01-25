/**
 * @file LpResult.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Result obtained from the LP solver.
 *
 * The output of the LP solver can be:
 * - LP_NO_RESULT: no result has been obtained yet.
 * - LP_UNSOLVED: the problem has not been solved. An error may have occurred.
 * - LP_INFEASIBLE: the problem is infeasible.
 * - LP_UNBOUNDED: the problem is unbounded.
 * - LP_OPTIMAL: the problem has been solved optimally.
 * - LP_DELTA_OPTIMAL: the problem has been solved optimally, but with a delta.
 */
#pragma once

#include <ostream>
#include <string>

namespace dlinear {

enum class LpResult {
  LP_NO_RESULT,      ///< No result has been obtained yet.
  LP_UNSOLVED,       ///< The problem has not been solved. An error may have occurred.
  LP_INFEASIBLE,     ///< The problem is infeasible.
  LP_UNBOUNDED,      ///< The problem is unbounded.
  LP_OPTIMAL,        ///< The problem has been solved optimally.
  LP_DELTA_OPTIMAL,  ///< The problem has been solved optimally, but with a delta.
};

LpResult parseLpResult(int res);
std::ostream &operator<<(std::ostream &os, const LpResult &lp_result);

}  // namespace dlinear
