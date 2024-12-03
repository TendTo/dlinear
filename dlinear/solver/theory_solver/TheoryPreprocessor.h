/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * TheoryPreprocessor class.
 */
#pragma once

#include <functional>
#include <string>
#include <unordered_set>

#include "dlinear/symbolic/literal.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/concepts.h"

namespace dlinear {

// Forward declaration
class TheorySolver;

/**
 * The theory preprocessor is a class that is used to preprocess the literals before invoking the solver.
 *
 * The preprocessing step is supposed to be very fast and correct, but not necessarily complete (exhaustive).
 * Hence, it may not detect all the conflicts in the set of literals.
 * The goal is to identify trivial inconsistencies and avoid invoking the solver for that iteration.
 */
class TheoryPreprocessor {
 public:
  /**
   * Construct a new Theory Preprocessor object for a given @p theory_solver.
   * @param theory_solver theory solver that will use this preprocessor
   * @param class_name name of the subclass of the theory preprocessor used
   */
  explicit TheoryPreprocessor(const TheorySolver& theory_solver, const std::string& class_name = "TheoryPreprocessor");
  virtual ~TheoryPreprocessor() = default;

  /** @getter{theory solver, TheoryPreprocessor} */
  [[nodiscard]] const TheorySolver& theory_solver() const { return theory_solver_; }
  /** @getter{statistics, TheoryPreprocessor} */
  [[nodiscard]] const IterationStats& stats() const { return stats_; }
  /** @getter{step at which the preprocessor will run, TheoryPreprocessor} */
  [[nodiscard]] virtual Config::ExecutionStep run_on_step() const = 0;
  /**
   * Check whether the preprocessor will run on the given @p step.
   * @param step step to check
   * @return true if the preprocessor will run on the given step
   * @return false if the preprocessor will not run on the given step
   */
  [[nodiscard]] bool WillRunOnStep(Config::ExecutionStep step) const;

  /**
   * Add the @p literals to the preprocessor.
   *
   * It may run some preliminary steps necessary to enable the literals later.
   * @tparam Iterable generic iterable containing literals (i.e. std::vector, std::set, std::span)
   * @param literals literals to add
   */
  template <SizedTypedIterable<Literal> Iterable>
  void AddLiterals(const Iterable& literals);
  /**
   * Add the @p lit literal to the preprocessor.
   *
   * It may run some preliminary steps necessary to enable the literal later.
   * @param lit literal to add
   */
  virtual void AddLiteral(const Literal& lit);
  /**
   * Add the @p var variable to the preprocessor.
   *
   * It may run some preliminary steps necessary to enable the variable later.
   * @param var variable to add
   */
  virtual void AddVariable(const Variable& var);

  /**
   * Enable the @p theory_literals in the preprocessor.
   *
   * The preprocessing will ensure that the @p theory_literals are not trivially inconsistent
   * with the current set of enabled literals.
   * If that is the case, an explanation is produced and used to invoke the @p conflict_cb .
   * @tparam Iterable generic iterable containing literals (i.e. std::vector, std::set, std::span)
   * @param theory_literals vector of literals to be enabled
   * @param conflict_cb callback to call when a conflict is detected. It will receive the explanation
   * @return true if no conflicts are detected at this step
   * @return false if a conflict is detected at this step
   */
  template <SizedTypedIterable<Literal> Iterable>
  bool EnableLiterals(const Iterable& theory_literals, const ConflictCallback& conflict_cb);
  /**
   * Enable the @p lit literal that had previously been added to the preprocessor.
   * @param lit literal to enable
   * @param conflict_cb callback to call when a conflict is detected. It will receive the explanation
   * @return true no conflicts was detected at this step
   * @return false if one or more conflicts were detected at this step
   */
  virtual bool EnableLiteral(const Literal& lit, const ConflictCallback& conflict_cb) = 0;

  /**
   * Run the preprocessing step on all the enabled literals.
   *
   * The preprocessor will run only if the @p current_step is compatible with its own execution step
   * set in the configuration
   * If a conflict is detected, the @p conflict_cb will be invoked with the explanation.
   * @param current_step current step of the execution
   * @param conflict_cb callback to call when a conflict is detected. It will receive the explanation
   * @return true if no conflicts was detected at this step
   * @return false if one or more conflicts were detected at this step
   */
  bool Process(Config::ExecutionStep current_step, const ConflictCallback& conflict_cb);

  /** Restore the preprocessor to the last checkpoint. */
  virtual void Backtrack() = 0;

 protected:
  /**
   * Run the preprocessing step on all the enabled literals.
   *
   * If a conflict is detected, the @p conflict_cb will be invoked with the explanation.
   * @param conflict_cb callback to call when a conflict is detected. It will receive the explanation
   * @return true if no conflicts was detected at this step
   * @return false if one or more conflicts were detected at this step
   */
  virtual bool ProcessCore(const ConflictCallback& conflict_cb) = 0;

  const TheorySolver& theory_solver_;  ///< Theory solver containing the variables and the literals
  IterationStats stats_;               ///< Statistics for the preprocessor
};

}  // namespace dlinear
