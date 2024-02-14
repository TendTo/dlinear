/**
 * @file SolverOutput.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Simple class that holds the output of the solver.
 * @todo Use a struct instead of a class.
 */
#pragma once

#include <string>
#include <utility>

#include "dlinear/libs/gmp.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Timer.h"

namespace dlinear {

/**
 * SmtSolver Result.
 * The solver can produce the following outputs:
 * - UNSOLVED: The solver has not been run.
 * - SAT: The context is satisfiable.
 * - DELTA_SAT: The context is delta-satisfiable.
 * - OPTIMAL: The context is optimal.
 * - DELTA_OPTIMAL: The context is delta-optimal.
 * - UNBOUNDED: The context is unbounded.
 * - INFEASIBLE: The context is infeasible.
 * - UNSAT: The context is unsatisfiable.
 * - UNKNOWN: Could not determine satisfiability.
 * - ERROR: An error occurred.
 */
enum class SolverResult {
  UNSOLVED,       // The solver has not yet been run.
  SKIP_SAT,       // The user asked to skip the satisfiability check.
  SAT,            // The problem is satisfiable.
  DELTA_SAT,      // The problem is delta-satisfiable.
  OPTIMAL,        // The optimization problem is optimal.
  DELTA_OPTIMAL,  // The optimization problem is delta-optimal.
  UNBOUNDED,      // The problem is unbounded.
  INFEASIBLE,     // The problem is infeasible.
  UNSAT,          // The problem is unsatisfiable.
  UNKNOWN,        // Could not determine satisfiability.
  ERROR,          // An error occurred.
};

struct SolverOutput {
  explicit SolverOutput(mpq_class _precision, bool _produce_models = false, bool _with_timings = false)
      : actual_precision{std::move(_precision)}, produce_models{_produce_models}, with_timings{_with_timings} {}

  [[nodiscard]] double precision_upper_bound() const;
  [[nodiscard]] bool is_sat() const {
    return result == SolverResult::SAT || result == SolverResult::DELTA_SAT || result == SolverResult::OPTIMAL ||
           result == SolverResult::DELTA_OPTIMAL;
  }

  [[nodiscard]] std::string ToString() const;

  Timer parser_timer{};
  Timer smt_solver_timer{};
  uint n_assertions{0};
  SolverResult result{SolverResult::UNSOLVED};
  mpq_class lower_bound{0};
  mpq_class upper_bound{0};
  Box model{};
  mpq_class actual_precision{0};
  bool produce_models{false};
  bool with_timings{false};
};

std::ostream &operator<<(std::ostream &os, const SolverResult &result);
std::ostream &operator<<(std::ostream &os, const SolverOutput &output);

}  // namespace dlinear
