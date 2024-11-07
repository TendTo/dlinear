/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "TheorySolver.h"

#include "dlinear/util/error.h"
#include "dlinear/util/logging.h"

namespace dlinear {

TheorySolver::TheorySolver(const PredicateAbstractor &predicate_abstractor, const std::string &class_name)
    : config_{predicate_abstractor.config()},
      is_consolidated_{false},
      predicate_abstractor_{predicate_abstractor},
      model_{config_.lp_solver()},
      stats_{config_.with_timings(), class_name, "Total time spent in CheckSat", "Total # of CheckSat"},
      preprocessor_{nullptr},
      propagator_{nullptr} {}

const Box &TheorySolver::model() const { return model_; }

void TheorySolver::AddLiterals() {
  for (const auto &[var, f] : predicate_abstractor_.var_to_formula_map()) AddLiteral(var, f);
}

void TheorySolver::AddLiterals(std::span<const Literal> literals) {
  for (const Literal &lit : literals) AddLiteral(lit.var, predicate_abstractor_[lit.var]);
}

bool TheorySolver::PreprocessFixedLiterals(const LiteralSet &fixed_literals, const ConflictCallback &conflict_cb) {
  DLINEAR_TRACE_FMT("TheorySolver::PreprocessFixedLiterals({})", fixed_literals);
  DLINEAR_ASSERT(is_consolidated_, "Fixed literals can be preprocessed only after consolidation");

  // No need to preprocess if there is no preprocessor
  if (preprocessor_ == nullptr) return true;
  bool res = true;
  for (const Literal &lit : fixed_literals) res &= preprocessor_->EnableLiteral(lit, conflict_cb);
  if (config_.actual_bound_propagation_frequency() == Config::PreprocessingRunningFrequency::ALWAYS ||
      config_.actual_bound_propagation_frequency() == Config::PreprocessingRunningFrequency::ON_FIXED) {
    res &= preprocessor_->Process(conflict_cb);
  }
  DLINEAR_TRACE_FMT("TheorySolver::PreprocessFixedLiterals() -> {}", res);
  return res;
}

bool TheorySolver::EnableLiterals(const std::span<const Literal> theory_literals, const ConflictCallback &conflict_cb) {
  bool res = true;
  for (const Literal &lit : theory_literals) {
    res &= EnableLiteral(lit, conflict_cb);
  }
  return res;
}

void TheorySolver::Consolidate(const Box &) {
  if (is_consolidated_) return;
  DLINEAR_DEBUG("TheorySolver::Consolidate()");
  is_consolidated_ = true;
}

TheoryResult TheorySolver::CheckSat(mpq_class *actual_precision, const ConflictCallback &conflict_cb) {
  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();
  return CheckSatCore(actual_precision, conflict_cb);
}

}  // namespace dlinear
