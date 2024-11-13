/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * SmtResult enum.
 */
#pragma once

#include <iosfwd>

namespace dlinear {

/** SmtSolver Result based on the result of the solver. */
enum class SmtResult {
  UNSOLVED,   ///< The solver has not yet been run.
  SKIP_SAT,   ///< The user asked to skip the satisfiability check.
  SAT,        ///< The problem is satisfiable.
  DELTA_SAT,  ///< The problem is delta-satisfiable.
  UNSAT,      ///< The problem is unsatisfiable.
  ERROR,      ///< An error occurred.
  TIMEOUT,    ///< The solver timed out.
};

/**
 * Relax the @p result of the SMT solver (i.e. transform SAT to DELTA_SAT).
 *
 * All other results are left unchanged.
 * @param result result to relax
 * @return relaxed result
 */
SmtResult operator~(SmtResult result);
std::ostream &operator<<(std::ostream &os, const SmtResult &result);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::SmtResult)

#endif
