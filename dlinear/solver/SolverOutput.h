/**
 * @file SolverOutput.h
 * @author dlinear
 * @date 16 Sep 2023
 * @copyright 2023 dlinear
 *
 * @brief Simple class that holds the output of the solver.
 *
 */
#pragma once

#include <string>
#include <utility>

#include "dlinear/libs/gmp.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Timer.h"

namespace dlinear {

/**
 * Solver Result.
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

class SolverOutput {
 public:
  explicit SolverOutput(mpq_class precision, bool produce_models = false, bool with_timings = false)
      : result_{SolverResult::UNSOLVED},
        actual_precision_{std::move(precision)},
        produce_models_{produce_models},
        with_timings_{with_timings} {}

  Timer &mutable_parser_timer() { return parser_timer_; }
  Timer &mutable_smt_solver_timer() { return smt_solver_timer_; }
  SolverResult &mutable_result() { return result_; }
  mpq_class &mutable_actual_precision() { return actual_precision_; }
  mpq_class &mutable_lower_bound() { return lower_bound_; }
  mpq_class &mutable_upper_bound() { return upper_bound_; }
  Box &mutable_model() { return model_; }
  bool &mutable_with_timings() { return with_timings_; }
  bool &mutable_produce_models() { return produce_models_; }
  uint &mutable_n_assertions() { return n_assertions_; }

  [[nodiscard]] double parser_time() const { return parser_timer_.seconds(); }
  [[nodiscard]] double smt_solver_time() const { return smt_solver_timer_.seconds(); }
  [[nodiscard]] SolverResult result() const { return result_; }
  [[nodiscard]] const mpq_class &actual_precision() const { return actual_precision_; }
  [[nodiscard]] double precision_upper_bound() const;
  [[nodiscard]] const mpq_class &lower_bound() const { return lower_bound_; }
  [[nodiscard]] const mpq_class &upper_bound() const { return upper_bound_; }
  [[nodiscard]] const Box &model() const { return model_; }
  [[nodiscard]] bool with_timings() const { return with_timings_; }
  [[nodiscard]] bool produce_models() const { return produce_models_; }
  [[nodiscard]] uint n_assertions() const { return n_assertions_; }
  [[nodiscard]] bool is_sat() const {
    return result_ == SolverResult::SAT || result_ == SolverResult::DELTA_SAT || result_ == SolverResult::OPTIMAL ||
           result_ == SolverResult::DELTA_OPTIMAL;
  }

  [[nodiscard]] std::string ToString() const;

 private:
  Timer parser_timer_{};
  Timer smt_solver_timer_{};
  uint n_assertions_{0};
  SolverResult result_{SolverResult::UNSOLVED};
  mpq_class lower_bound_{0};
  mpq_class upper_bound_{0};
  Box model_{};
  mpq_class actual_precision_;
  bool produce_models_;
  bool with_timings_;
};

std::ostream &operator<<(std::ostream &os, const SolverResult &result);
std::ostream &operator<<(std::ostream &os, const SolverOutput &output);

}  // namespace dlinear
