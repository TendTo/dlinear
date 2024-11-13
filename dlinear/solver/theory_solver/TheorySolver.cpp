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
      pa_{predicate_abstractor},
      model_{config_.lp_solver()},
      stats_{config_.with_timings(), class_name, "Total time spent in CheckSat", "Total # of CheckSat"},
      preprocessor_{nullptr},
      propagator_{nullptr} {}

const Box &TheorySolver::model() const { return model_; }

void TheorySolver::AddLiterals() {
  for (const auto &[var, f] : pa_.var_to_formula_map()) AddLiteral(var, f);
}

void TheorySolver::AddLiterals(std::span<const Literal> literals) {
  for (const Literal &lit : literals) AddLiteral(lit.var, pa_[lit.var]);
}
template <TypedIterable<Literal> Iterable>
bool TheorySolver::PreprocessFixedLiterals(const Iterable &fixed_literals, const ConflictCallback &conflict_cb) {
  DLINEAR_DEBUG_FMT("TheorySolver::PreprocessFixedLiterals(#fixed_literals = {})", fixed_literals.size());
  DLINEAR_TRACE_FMT("TheorySolver::PreprocessFixedLiterals({})", fixed_literals);
  DLINEAR_ASSERT(is_consolidated_, "Fixed literals can be preprocessed only after consolidation");

  // No need to preprocess if there is no preprocessor
  bool res = true;
  for (const Literal &lit : fixed_literals) {
    res &= EnableLiteral(lit, conflict_cb);
  }
  if (preprocessor_ != nullptr) {
    DLINEAR_DEBUG("TheorySolver::PreprocessFixedLiterals: running preprocessor");
    res &= preprocessor_->ProcessFixed(conflict_cb);
  }

  DLINEAR_TRACE_FMT("TheorySolver::PreprocessFixedLiterals() -> {}", res);
  if (res) {
    for (const Literal &lit : fixed_literals) enabled_literals_checkpoint_.insert(lit.var);
    CreateCheckpoint();
  }
  DLINEAR_DEV_FMT("TheorySolver::PreprocessFixedLiterals() -> {}", res);
  return res;
}

template <TypedIterable<Literal> Iterable>
bool TheorySolver::EnableLiterals(const Iterable &theory_literals, const ConflictCallback &conflict_cb) {
  bool res = true;
  for (const Literal &lit : theory_literals) {
    res &= EnableLiteral(lit, conflict_cb);
  }
  return res;
}

void TheorySolver::Consolidate(const Box &model) {
  if (is_consolidated_) return;
  DLINEAR_DEBUG("TheorySolver::Consolidate()");
  is_consolidated_ = true;
  model_ = model;
  CreateCheckpoint();
}

TheoryResult TheorySolver::CheckSat(mpq_class *actual_precision, const ConflictCallback &conflict_cb) {
  DLINEAR_DEV("TheorySolver::CheckSat");
  if (preprocessor_ != nullptr) {
    const bool success = preprocessor_->Process(conflict_cb);
    if (!success) return TheoryResult::UNSAT;
  }
  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();
  return CheckSatCore(actual_precision, conflict_cb);
}

void TheorySolver::Propagate(const AssertCallback &assert_cb) {
  // Temporarily disable to study the effect of guided constraints
  // The propagator is disabled or absent (maybe this theory does not have a propagator implemented)
  if (config_.actual_bound_implication_frequency() == Config::PreprocessingRunningFrequency::NEVER ||
      propagator_ == nullptr) {
    return;
  }
  // Add some theory constraints to the SAT solver (e.g. (x > 0) => (x > -1))
  propagator_->Propagate(assert_cb);
}
void TheorySolver::Backtrack() {
  DLINEAR_TRACE("OldTestLpSolver::Backtrack()");
  DLINEAR_ASSERT(is_consolidated_, "The solver  must be consolidate before resetting it");
  // Backtrack all the constraints added with the last iteration, keeping the fixed ones
  // preprocessor_->Backtrack();
}

template bool TheorySolver::PreprocessFixedLiterals(const std::vector<Literal> &, const ConflictCallback &);
template bool TheorySolver::PreprocessFixedLiterals(const LiteralSet &, const ConflictCallback &);
template bool TheorySolver::PreprocessFixedLiterals(const std::span<Literal> &, const ConflictCallback &);
template bool TheorySolver::EnableLiterals(const std::vector<Literal> &, const ConflictCallback &);
template bool TheorySolver::EnableLiterals(const LiteralSet &, const ConflictCallback &);
template bool TheorySolver::EnableLiterals(const std::span<Literal> &, const ConflictCallback &);

}  // namespace dlinear
