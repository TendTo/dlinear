/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * TheoryPropagator class.
 */
#pragma once

#include <functional>
#include <string>

#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Stats.h"

namespace dlinear {

// Forward declarations
class TheorySolver;

class TheoryPropagator {
 public:
  explicit TheoryPropagator(const TheorySolver& theory_solver, const std::string& class_name = "TheoryPropagator");
  virtual ~TheoryPropagator() = default;

  /** @getter{theory solver, TheoryPropagator} */
  [[nodiscard]] const TheorySolver& theory_solver() const { return theory_solver_; }
  /** @getter{statistics, TheoryPropagator} */
  [[nodiscard]] const IterationStats& stats() const { return stats_; }
  /** @getter{step at which the propagator will run, TheoryPropagator} */
  [[nodiscard]] virtual Config::ExecutionStep run_on_step() const = 0;
  /**
   * Check whether the preprocessor will run on the given @p step.
   * @param step step to check
   * @return true if the preprocessor will run on the given step
   * @return false if the preprocessor will not run on the given step
   */
  [[nodiscard]] bool WillRunOnStep(Config::ExecutionStep step) const;

  /**
   * Use the current set of literals to propagate new literals.
   *
   * The propagator will run only if the @p current_step is compatible with its own execution step
   * set in the configuration
   * The new implied literals are passed to the @p assert_cb callback to be asserted and will guide the SAT solver.
   * @param current_step current execution step
   * @param assert_cb callback to call when a new literal can be implied from the current set of literals
   */
  void Propagate(Config::ExecutionStep current_step, const AssertCallback& assert_cb);

 protected:
  /**
   * Use the current set of literals to propagate new literals.
   *
   * The new implied literals are passed to the @p assert_cb callback to be asserted and will guide the SAT solver.
   * @param assert_cb callback to call when a new literal can be implied from the current set of literals
   */
  virtual void PropagateCore(const AssertCallback& assert_cb) = 0;

  const TheorySolver& theory_solver_;
  IterationStats stats_;
};

}  // namespace dlinear
