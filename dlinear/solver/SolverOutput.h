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

#include "dlinear/libs/gmp.h"
#include "dlinear/util/Box.h"

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
 * - UNFEASIBLE: The context is unfeasible.
 * - UNSAT: The context is unsatisfiable.
 * - UNKNOWN: Could not determine satisfiability.
 * - ERROR: An error occurred.
 */
enum class SolverResult {
  UNSOLVED,       // The solver has not yet been run.
  SAT,            // The problem is satisfiable.
  DELTA_SAT,      // The problem is delta-satisfiable.
  OPTIMAL,        // The optimization problem is optimal.
  DELTA_OPTIMAL,  // The optimization problem is delta-optimal.
  UNBOUNDED,      // The problem is unbounded.
  UNFEASIBLE,     // The problem is unfeasible.
  UNSAT,          // The problem is unsatisfiable.
  UNKNOWN,        // Could not determine satisfiability.
  ERROR,          // An error occurred.
};

class SolverOutput {
 public:
  explicit SolverOutput(mpq_class precision, bool produce_models = false, bool with_timings = false)
      : actual_precision_{precision}, produce_models_{produce_models}, with_timings_{with_timings} {}

  SolverResult result() const { return result_; }
  mpq_class &mutable_actual_precision() { return actual_precision_; }
  mpq_class &mutable_lower_bound() { return lower_bound_; }
  mpq_class &mutable_upper_bound() { return upper_bound_; }
  Box &mutable_model() { return model_; }
  bool &mutable_with_timings() { return with_timings_; }
  bool &mutable_produce_models() { return produce_models_; }

  SolverResult &mutable_result() { return result_; }
  const mpq_class &actual_precision() const { return actual_precision_; }
  double precision_upper_bound() const;
  const mpq_class &lower_bound() const { return lower_bound_; }
  const mpq_class &upper_bound() const { return upper_bound_; }
  const Box &model() const { return model_; }
  bool with_timings() const { return with_timings_; }
  bool produce_models() const { return produce_models_; }

  std::string ToString() const;

 private:
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
