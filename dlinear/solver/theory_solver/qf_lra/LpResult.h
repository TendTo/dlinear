/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * LpResult enum.
 */
#pragma once

#include <ostream>

namespace dlinear {

/** Result of running the LP solver over the input problem. */
enum class LpResult {
  LP_NO_RESULT,      ///< No result has been obtained yet.
  LP_UNSOLVED,       ///< The problem has not been solved. An error may have occurred.
  LP_INFEASIBLE,     ///< The problem is infeasible.
  LP_UNBOUNDED,      ///< The problem is unbounded.
  LP_OPTIMAL,        ///< The problem has been solved optimally.
  LP_DELTA_OPTIMAL,  ///< The problem has been solved optimally, but with a delta.
};

/**
 * Parse the result from the returned integer.
 * @param res return code
 * @return corresponding result
 */
LpResult parseLpResult(int res);
std::ostream &operator<<(std::ostream &os, const LpResult &lp_result);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::LpResult)

#endif
