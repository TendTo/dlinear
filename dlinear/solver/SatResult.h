/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * SatResult enum.
 */
#pragma once

#include <ostream>

namespace dlinear {

/**
 * Result of running the theory solver over the literals decided by the SAT solver.
 * It describes the result the solver was able to produce on the input problem for the current iteration.
 */
enum class SatResult {
  SAT_NO_RESULT,          ///< No result has been obtained yet.
  SAT_UNSOLVED,           ///< The problem has not been solved. An error may have occurred.
  SAT_UNSATISFIABLE,      ///< The problem is unsatisfiable.
  SAT_SATISFIABLE,        ///< The problem is satisfiable.
  SAT_DELTA_SATISFIABLE,  ///< The problem is satisfiable, but with a delta >= 0.
};

std::ostream &operator<<(std::ostream &os, const SatResult &sat_result);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::SatResult)

#endif
