/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * LpResult enum.
 */
#pragma once

#include <iosfwd>

namespace dlinear {

enum class LpResult {
  UNSOLVED,       ///< The solver has not yet been run.
  OPTIMAL,        ///< The problem is optimal.
  DELTA_OPTIMAL,  ///< The delta-relaxation of the problem is optimal.
  UNBOUNDED,      ///< The problem is unbounded
  INFEASIBLE,     ///< The problem is infeasible.
  ERROR,          ///< An error occurred.
};

/**
 * Relax the @p result of the theory solver (i.e. transform SAT to DELTA_SAT).
 *
 * All other results are left unchanged.
 * @param result result to relax
 * @return relaxed result
 */
LpResult operator~(LpResult result);
std::ostream &operator<<(std::ostream &os, LpResult result);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::LpResult)

#endif
