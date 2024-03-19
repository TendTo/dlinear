/**
 * @file SmtSolverOutput.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Simple class that holds the output of the solver.
 */
#pragma once

#include <string>
#include <utility>

#include "dlinear/libs/gmp.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"

namespace dlinear {

/** SmtSolver Result based on the result of the solver. */
enum class SolverResult {
  UNSOLVED,       ///< The solver has not yet been run.
  SKIP_SAT,       ///< The user asked to skip the satisfiability check.
  SAT,            ///< The problem is satisfiable.
  DELTA_SAT,      ///< The problem is delta-satisfiable.
  OPTIMAL,        ///< The optimization problem is optimal.
  DELTA_OPTIMAL,  ///< The optimization problem is delta-optimal.
  UNBOUNDED,      ///< The problem is unbounded.
  INFEASIBLE,     ///< The problem is infeasible.
  UNSAT,          ///< The problem is unsatisfiable.
  UNKNOWN,        ///< Could not determine satisfiability.
  ERROR,          ///< An error occurred.
};

/**
 * SmtSolverOutput struct.
 *
 * Contains the output of the solver, such as the result of the computation as well as some statistics.
 */
struct SmtSolverOutput {
  SmtSolverOutput() = delete;
  /**
   * Construct a new SmtSolverOutput object.
   * @param config configuration of the solver. Used to initialise a few static parameters
   */
  explicit SmtSolverOutput(const Config &config)
      : precision{config.precision()},
        actual_precision{config.precision()},
        produce_models{config.produce_models()},
        with_timings{config.with_timings()} {}

  /**
   * Return the precision upper bound.
   * @return precision upper bound
   */
  [[nodiscard]] double precision_upper_bound() const;
  /**
   * Return whether the problem is satisfiable or some variant of it.
   * @return true if the problem is satisfiable
   * @return false if the problem is not satisfiable
   */
  [[nodiscard]] bool is_sat() const {
    return result == SolverResult::SAT || result == SolverResult::DELTA_SAT || result == SolverResult::OPTIMAL ||
           result == SolverResult::DELTA_OPTIMAL;
  }
  /**
   * Exit code of the solver to return to the user.
   * @return 0 if the problem is satisfiable
   * @return 1 if the problem is not satisfiable
   * @return 2 if the solver was unable to determine the satisfiability
   * @return 3 if an error was detected
   * @return 4 any other case
   */
  [[nodiscard]] int exit_code() const;

  /**
   * Return a string representation of the output.
   * @return string representation
   */
  [[nodiscard]] std::string ToString() const;

  IterationStats sat_stats{DLINEAR_INFO_ENABLED, ""};     ///< Statistics about the satisfiability check
  IterationStats theory_stats{DLINEAR_INFO_ENABLED, ""};  ///< Statistics about the theory check
  Timer total_timer{};                                    ///< Timer keeping track of the total time spent in the solver
  Timer parser_timer{};                                   ///< Timer keeping track of the time spent parsing the input
  Timer smt_solver_timer{};                               ///< Timer keeping track of the time spent in the SMT solver
  uint n_assertions{0};                                   ///< Number of assertions in the input
  SolverResult result{SolverResult::UNSOLVED};            ///< Result of the computation
  mpq_class lower_bound{0};                               ///< Lower bound of the result
  mpq_class upper_bound{0};                               ///< Upper bound of the result
  Box model{};                                            ///< Model of the result
  const mpq_class precision;                              ///< User-provided precision of the computation
  mpq_class actual_precision;  ///< Actual precision of the computation. Always < than precision
  const bool produce_models;   ///< Whether the solver should produce models
  const bool with_timings;     ///< Whether the solver should show timings
};

std::ostream &operator<<(std::ostream &os, const SolverResult &result);
std::ostream &operator<<(std::ostream &os, const SmtSolverOutput &output);

}  // namespace dlinear
