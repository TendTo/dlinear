/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * SmtSolverOutput struct.
 */
#pragma once

#include <chrono>
#include <iosfwd>
#include <string>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/SmtResult.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"

namespace dlinear {

/**
 * Data struct containing the output of the solver, such as the result of the computation as well as some statistics.
 */
struct SmtSolverOutput {
  SmtSolverOutput() = delete;
  /**
   * Construct a new SmtSolverOutput object.
   * @param config configuration of the solver. Used to initialise a few static parameters
   */
  explicit SmtSolverOutput(const Config &config)
      : produce_models{config.produce_models()},
        with_timings{config.with_timings()},
        model{config.lp_solver()},
        complete_model{config.lp_solver()},
        precision{config.precision()},
        actual_precision{config.precision()} {}

  /** @getter{precision, upper bound} */
  [[nodiscard]] double precision_upper_bound() const;
  /** @checker{satisfiable, problem or its delta-relaxation} */
  [[nodiscard]] bool is_sat() const { return result == SmtResult::SAT || result == SmtResult::DELTA_SAT; }
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
   * Check if the result of the computation matches the expectation.
   *
   * If the solver is running in complete mode, the results are expected to be the same.
   * Otherwise, a relaxation of the result is allowed.
   * @param expectation expected result
   * @return true if the result matches the expectation
   * @return false if the result does not match the expectation
   */
  [[nodiscard]] bool matches_expectation(SmtResult expectation) const;

  /**
   * Add the statistics of a component of the solver to the output.
   *
   * They will be displayed in the same order they were added.
   * @param stats statistics to add
   */
  void add_iteration_stats(const IterationStats &stats) { iteration_stats.push_back(stats); }

  bool produce_models;  ///< Whether the solver should produce models
  bool with_timings;    ///< Whether the solver should show timings

  Stats parser_stats{with_timings, ""};           ///< Statistics about the solver
  std::vector<IterationStats> iteration_stats{};  ///< Statistics about many components of the solver

  Timer smt_solver_timer{};               ///< Timer keeping track of the time spent in the SMT solver
  unsigned int n_assertions{0};           ///< Number of assertions in the input
  SmtResult result{SmtResult::UNSOLVED};  ///< Result of the computation
  mpq_class lower_bound{0};               ///< Lower bound of the result
  mpq_class upper_bound{0};               ///< Upper bound of the result
  Box model;                              ///< Model of the result
  Box complete_model;                     ///< Model of the result that include the auxilary variables introduced
  mpq_class precision;                    ///< User-provided precision of the computation
  mpq_class actual_precision;             ///< Actual precision of the computation. Always <= than precision
};

std::ostream &operator<<(std::ostream &os, const SmtSolverOutput &output);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::SmtSolverOutput)

#endif
