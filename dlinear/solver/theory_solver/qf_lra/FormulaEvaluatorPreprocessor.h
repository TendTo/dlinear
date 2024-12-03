/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * FormulaEvaluatorPreprocessor class.
 */
#pragma once

#include <map>
#include <memory>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

#include "dlinear/solver/theory_solver/TheoryPreprocessor.h"
#include "dlinear/solver/theory_solver/qf_lra/BoundVector.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/environment.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Graph.hpp"

namespace dlinear {

// Forward declaration
class TheorySolver;

class FormulaEvaluatorPreprocessor final : public TheoryPreprocessor {
 public:
  /**
   * Construct a new FormulaEvaluatorPreprocessor object using the @p theory_solver.
   * @param theory_solver theory solver that will use this preprocessor
   * @param var_bounds bounds over each real variable. Shared with other preprocessors
   * @param env environment containing the variable's values. Shared with other preprocessors
   * @param class_name name of the subclass of the theory preprocessor used
   */
  FormulaEvaluatorPreprocessor(const TheorySolver& theory_solver, const std::shared_ptr<BoundVectorMap>& var_bounds,
                               const std::shared_ptr<Environment>& env,
                               const std::string& class_name = "FormulaEvaluatorPreprocessor");

  [[nodiscard]] Config::ExecutionStep run_on_step() const override;

  /** @getter{var_bounds, formula evaluator preprocessor} */
  [[nodiscard]] const BoundVectorMap& var_bounds() const { return *var_bounds_; }
  /** @getter{environment, formula evaluator preprocessor} */
  [[nodiscard]] const Environment& env() const { return *env_; }

  bool EnableLiteral(const Literal& lit, const ConflictCallback& conflict_cb) override;
  bool ProcessCore(const ConflictCallback& conflict_cb) override;
  void Backtrack() override;

 protected:
  /**
   * Check if the @p lit corresponds to a formula that should be evaluated.
   *
   * A formula can be evaluated if:
   * - All the free variables it contains are present in the environment @re env_
   * @param lit lit to check
   * @return true if the formula can be evaluated
   * @return false if the formula cannot be evaluated
   */
  [[nodiscard]] bool ShouldEvaluateFormula(const Literal& lit) const;
  /**
   * Check if the @p formula should be evaluated.
   *
   * A formula can be evaluated if:
   * - All the free variables it contains are present in the environment @re env_
   * @param formula formula to check
   * @return true if the formula can be evaluated
   * @return false if the formula cannot be evaluated
   */
  [[nodiscard]] bool ShouldEvaluateFormula(const Formula& formula) const;

  /**
   * Go through all the @ref var_bounds_ to set the @ref env_.
   *
   * Every time a variable has an active equality bound, the value is set in the environment @ref env_ .
   */
  void SetEnvironmentFromBounds();

  /**
   * Evaluate all the formulas corresponding to the @ref enabled_literals_ .
   *
   * After updating the environment @ref env_ using the bounds @ref var_bounds_ ,
   * evaluate all formulae where all the free variables are present in the environment, making sure they are satisfied.
   * If a formula is not satisfied, a conflict is detected, and the @p conflict_cb is invoked with the explanation,
   * which is built using the bounds @ref var_bounds_ for each of the involved variables.
   * @param conflict_cb callback to call when a conflict is detected. It will receive the explanation
   * @return true if no conflicts are detected at this step
   * @return false if a conflict is detected at this step
   */
  bool EvaluateFormulas(const ConflictCallback& conflict_cb) const;

  /**
   * Notify of the detected conflict during the evaluation of the @p formula
   * by calling the @p conflict_cb with the explanation.
   * @param lit literal that caused the conflict. It is part of the explanation
   * @param formula formula that caused the conflict. Corresponding to the @p lit
   * @param conflict_cb callback to call when a conflict is detected. It will receive the explanation
   */
  void NotifyConflict(const Literal& lit, const Formula& formula, const ConflictCallback& conflict_cb) const;

 private:
  std::shared_ptr<BoundVectorMap> var_bounds_;  ///< Bounds over each real variable. Shared with other preprocessors
  std::shared_ptr<Environment> env_;  ///< Environment containing the variable's values. Shared with other preprocessors

  LiteralSet enabled_literals_;  ///< Literals that should be evaluated
};

std::ostream& operator<<(std::ostream& os, const FormulaEvaluatorPreprocessor& preprocessor);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::FormulaEvaluatorPreprocessor)

#endif
