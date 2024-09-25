/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * Describes the result of the SAT solver using an enum class.
 *
 * The SAT solver can return the following results:
 * - SAT_NO_RESULT: no result has been obtained yet.
 * - SAT_UNSOLVED: the problem has not been solved. An error may have occurred.
 * - SAT_UNSATISFIABLE: the problem is unsatisfiable.
 * - SAT_SATISFIABLE: the problem is satisfiable.
 * - SAT_DELTA_SATISFIABLE: the problem is satisfiable, but with a delta.
 */
#pragma once

#include <ostream>

namespace dlinear {

/**
 * Result of running the theory solver over the literals decided by the SAT solver.
 * It describes the viewpoint of the solver on the input problem for the current iteration.
 */
enum class SatResult {
  SAT_NO_RESULT,          ///< No result has been obtained yet.
  SAT_UNSOLVED,           ///< The problem has not been solved. An error may have occurred.
  SAT_UNSATISFIABLE,      ///< The problem is unsatisfiable.
  SAT_SATISFIABLE,        ///< The problem is satisfiable.
  SAT_DELTA_SATISFIABLE,  ///< The problem is satisfiable, but with a delta.
};

std::ostream &operator<<(std::ostream &os, const SatResult &sat_result);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::SatResult)

#endif
