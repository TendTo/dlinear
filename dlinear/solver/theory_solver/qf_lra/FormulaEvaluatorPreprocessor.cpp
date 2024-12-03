/**
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "FormulaEvaluatorPreprocessor.h"

#include <unordered_set>

#include "QfLraTheorySolver.h"
#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/theory_solver/TheorySolver.h"
#include "dlinear/util/error.h"

namespace dlinear {

FormulaEvaluatorPreprocessor::FormulaEvaluatorPreprocessor(const TheorySolver& theory_solver,
                                                           const std::shared_ptr<BoundVectorMap>& var_bounds,
                                                           const std::shared_ptr<Environment>& env,
                                                           const std::string& class_name)
    : TheoryPreprocessor{theory_solver, class_name}, var_bounds_{var_bounds}, env_{env} {
  DLINEAR_ASSERT(var_bounds_ != nullptr, "The var_bounds must not be null");
  DLINEAR_ASSERT(env_ != nullptr, "The env must not be null");
}

Config::ExecutionStep FormulaEvaluatorPreprocessor::run_on_step() const {
  return theory_solver_.config().actual_formula_evaluation_preprocess_step();
}

bool FormulaEvaluatorPreprocessor::EnableLiteral(const Literal& lit, const ConflictCallback&) {
  DLINEAR_TRACE_FMT("FormulaEvaluatorPreprocessor::EnableConstraint({})", lit);
  // If the literal only contains one variable there is no need to evaluate it
  if (theory_solver_.predicate_abstractor()[lit.var].GetFreeVariables().size() <= 1) return true;
  enabled_literals_.emplace(lit);
  return true;
}

bool FormulaEvaluatorPreprocessor::ProcessCore(const ConflictCallback& conflict_cb) {
  DLINEAR_TRACE("FormulaEvaluatorPreprocessor::Process()");
  // Sync the local var bounds with the ones from the theory solver if it is still empty
  if (var_bounds_->empty()) *var_bounds_ = static_cast<const QfLraTheorySolver&>(theory_solver_).vars_bounds();
  // Sync the environment with the active equality bounds from the var bounds if it is still empty
  if (env_->empty()) SetEnvironmentFromBounds();
  const bool no_conflict = EvaluateFormulas(conflict_cb);
  DLINEAR_DEBUG_FMT("FormulaEvaluatorPreprocessor::Process no conflict found -> {}", no_conflict);
  return no_conflict;
}

void FormulaEvaluatorPreprocessor::Backtrack() {
  if (!env_->empty()) *env_ = Environment{};
  var_bounds_->clear();
  enabled_literals_.clear();
}
void FormulaEvaluatorPreprocessor::SetEnvironmentFromBounds() {
  for (const auto& [var, bound] : *var_bounds_) {
    const mpq_class* const active_bound = bound.GetActiveEqualityBound();
    if (active_bound == nullptr) continue;
    if (env_->contains(var)) {
      DLINEAR_ASSERT(env_->at(var) == *active_bound, "No conflict should arise from this assignment");
      continue;
    }
    (*env_)[var] = *active_bound;
  }
}
bool FormulaEvaluatorPreprocessor::ShouldEvaluateFormula(const Literal& lit) const {
  DLINEAR_TRACE_FMT("BoundPreprocessor::ShouldEvaluate({})", lit);
  const Formula& formula = theory_solver_.predicate_abstractor()[lit.var];
  return ShouldEvaluateFormula(formula);
}
bool FormulaEvaluatorPreprocessor::ShouldEvaluateFormula(const Formula& formula) const {
  DLINEAR_TRACE_FMT("BoundPreprocessor::ShouldEvaluate({})", formula);
  // All free variables must be in the environment
  return std::all_of(formula.GetFreeVariables().begin(), formula.GetFreeVariables().end(),
                     [this](const Variable& v) { return env_->contains(v); });
}
bool FormulaEvaluatorPreprocessor::EvaluateFormulas(const ConflictCallback& conflict_cb) const {
  bool no_conflict = true;
  for (const Literal& lit : enabled_literals_) {
    const Formula& formula = theory_solver_.predicate_abstractor()[lit.var];
    if (!ShouldEvaluateFormula(formula)) continue;
    const bool satisfied = formula.Evaluate(*env_) == lit.truth;
    if (!satisfied) {
      DLINEAR_DEBUG_FMT("FormulaEvaluatorPreprocessor::EvaluateFormulas: {} => FAIL", lit);
      NotifyConflict(lit, formula, conflict_cb);
      no_conflict = false;
    }
  }
  return no_conflict;
}
void FormulaEvaluatorPreprocessor::NotifyConflict(const Literal& lit, const Formula& formula,
                                                  const ConflictCallback& conflict_cb) const {
  DLINEAR_TRACE_FMT("BoundCheckerPreprocessor::FormulaViolationExplanation({})", formula);
  LiteralSet explanation;
  explanation.insert(lit);
  for (const auto& var : formula.GetFreeVariables()) {
    DLINEAR_ASSERT(env_->contains(var), "All free variables must be in the environment");
    var_bounds_->at(var).GetActiveExplanation(explanation);
  }
#if DEBUGGING_PREPROCESSOR
  const bool res = check_explanation(*this, explanation);
  if (!res) {
    for (const auto& var : formula.GetFreeVariables()) {
      // fmt::println("Explanation origins: {} --> {}", var, GetExplanationOrigins(var));
      LiteralSet ex;
      GetExplanation(var, ex);
      // fmt::println("Explanation: {} --> {}", var, ex);
    }
    for (const auto& var_name : {"x_87", "x_97"}) {
      Variable var = find_variable(*this, var_name);
      // fmt::println("Explanation origins: {} --> {}", var, GetExplanationOrigins(var));
      LiteralSet ex;
      GetExplanation(var, ex);
      // fmt::println("Explanation: {} --> {}", var, ex);
    }
    DLINEAR_ASSERT(res, "Explanation must be valid");
  }
#endif
  conflict_cb(explanation);
}

std::ostream& operator<<(std::ostream& os, const FormulaEvaluatorPreprocessor& preprocessor) {
  return os << "FormulaEvaluatorPreprocessor{env_ = " << preprocessor.env() << "}";
}

}  // namespace dlinear
