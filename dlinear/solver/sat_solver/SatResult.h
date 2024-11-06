/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * SatResult enum.
 */
#pragma once

#include <iosfwd>

namespace dlinear {

enum class SatResult {
  UNSOLVED,   ///< The solver has not yet been run.
  SAT,        ///< The problem is satisfiable.
  DELTA_SAT,  ///< The problem is delta-satisfiable.
  UNSAT,      ///< The problem is unsatisfiable.
  ERROR,      ///< An error occurred.
};

/**
 * Relax the @p result of the sat solver (i.e. transform SAT to DELTA_SAT).
 *
 * All other results are left unchanged.
 * @param result result to relax
 * @return relaxed result
 */
SatResult operator~(SatResult result);
std::ostream &operator<<(std::ostream &os, SatResult result);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::SatResult)

#endif
