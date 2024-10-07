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
#include "dlinear/solver/LpResult.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"

namespace dlinear {

/** SmtSolver Result based on the result of the solver. */
enum class SmtResult {
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

SmtResult parse_smt_result(SatResult sat_result);
SmtResult parse_smt_result(LpResult lp_result);

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
    return result == SmtResult::SAT || result == SmtResult::DELTA_SAT || result == SmtResult::OPTIMAL ||
           result == SmtResult::DELTA_OPTIMAL;
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
   * Check if the result of the computation matches the expectation.
   *
   * If the solver is running in complete mode, the results are expected to be the same.
   * Otherwise, a relaxation of the result is allowed.
   * @param expectation expected result
   * @return true if the result matches the expectation
   * @return false if the result does not match the expectation
   */
  [[nodiscard]] bool matches_expectation(SmtResult expectation) const;

  bool produce_models;  ///< Whether the solver should produce models
  bool with_timings;    ///< Whether the solver should show timings

  Stats parser_stats{with_timings, ""};                         ///< Statistics about the solver
  IterationStats ite_stats{with_timings, ""};                   ///< Statistics about the if-then-else simplifier
  IterationStats cnfizer_stats{with_timings, ""};               ///< Statistics about the formula cnfizer
  IterationStats predicate_abstractor_stats{with_timings, ""};  ///< Statistics about the predicate abstractor
  IterationStats sat_stats{with_timings, ""};                   ///< Statistics about the satisfiability check
  IterationStats theory_stats{with_timings, ""};                ///< Statistics about the theory check
  IterationStats preprocessor_stats{with_timings, ""};          ///< Statistics about the bound preprocessor

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

std::ostream &operator<<(std::ostream &os, const SmtResult &result);
std::ostream &operator<<(std::ostream &os, const SmtSolverOutput &output);

}  // namespace dlinear
