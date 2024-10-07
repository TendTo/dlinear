/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "TheorySolver.h"

#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

TheorySolver::TheorySolver(const PredicateAbstractor &predicate_abstractor, const std::string &class_name)
    : config_{predicate_abstractor.config()},
      is_consolidated_{false},
      predicate_abstractor_{predicate_abstractor},
      fixed_preprocessor_{predicate_abstractor},
      preprocessor_{predicate_abstractor},
      model_{config_.lp_solver()},
      stats_{config_.with_timings(), class_name, "Total time spent in CheckSat", "Total # of CheckSat"} {}

const Box &TheorySolver::model() const { return model_; }
std::set<Literal> TheorySolver::enabled_literals() const {
  std::set<Literal> enabled_lits{};
  for (std::size_t i = 0; i < theory_row_to_lit_.size(); ++i) {
    if (theory_rows_state_[i]) enabled_lits.insert(theory_row_to_lit_[i]);
  }
  for (const auto &[var, bound] : preprocessor_.theory_bounds()) {
    const BoundIterator it = bound.GetActiveBounds();
    it.explanation(enabled_lits);
  }
  return enabled_lits;
}

void TheorySolver::AddLiterals() {
  theory_row_to_lit_.reserve(predicate_abstractor_.var_to_formula_map().size());
  for (const auto &[var, f] : predicate_abstractor_.var_to_formula_map()) AddLiteral(var, f);
}

TheorySolver::Explanations TheorySolver::PreprocessFixedLiterals(const LiteralSet &fixed_literals) {
  DLINEAR_TRACE_FMT("TheorySolver::PreprocessFixedLiterals({})", fixed_literals);
  DLINEAR_ASSERT(is_consolidated_, "Fixed literals can be preprocessed only after consolidation");
  Explanations explanations{};
  for (const Literal &lit : fixed_literals) fixed_preprocessor_.EnableLiteral(lit, explanations);
  if (config_.actual_bound_propagation_frequency() == Config::PreprocessingRunningFrequency::ALWAYS ||
      config_.actual_bound_propagation_frequency() == Config::PreprocessingRunningFrequency::ON_FIXED) {
    fixed_preprocessor_.Process(explanations);
  }
  preprocessor_.Clear(fixed_preprocessor_);
  DLINEAR_TRACE_FMT("TheorySolver::PreprocessFixedLiterals() -> {}", explanations);
  return explanations;
}

TheorySolver::Explanations TheorySolver::EnableLiterals(const std::span<const Literal> theory_literals) {
  Explanations explanations{};
  for (const Literal &lit : theory_literals) {
    const Explanations explanation{EnableLiteral(lit)};
    // Check if the literal that was just enabled is conflicting with the current model.
    // If so, return the explanation containing a superset of the conflicting literals
    explanations.insert(explanation.begin(), explanation.end());
  }
  return explanations;
}

void TheorySolver::UpdateExplanations(Explanations &explanations) {
  DLINEAR_TRACE("TheorySolver::UpdateExplanation()");
  LiteralSet explanation{};
  UpdateExplanation(explanation);
  explanations.insert(explanation);
}

void TheorySolver::Consolidate(const Box &) {
  if (is_consolidated_) return;
  DLINEAR_DEBUG("TheorySolver::Consolidate()");
  theory_rows_state_.resize(theory_row_to_lit_.size(), false);
  is_consolidated_ = true;
}

void TheorySolver::Reset() {
  DLINEAR_TRACE("TheorySolver::Reset()");
  DLINEAR_ASSERT(is_consolidated_, "The solver  must be consolidate before resetting it");
  // Clear constraint bounds, keeping only the fixed ones
  preprocessor_.Clear(fixed_preprocessor_);
  // Disable all rows
  theory_rows_state_.assign(theory_rows_state_.size(), false);
}

#ifndef NDEBUG
void TheorySolver::DumpEnabledLiterals() {
  fmt::println("(set-logic QF_LRA)");
  for (const auto &[var, bound] : preprocessor_.theory_bounds()) {
    fmt::println("(declare-const {} Real)", var);
  }
  for (const auto &lit : enabled_literals()) {
    fmt::println("(assert {})", lit.truth ? predicate_abstractor_[lit.var].to_smt2_string()
                                          : (!predicate_abstractor_[lit.var]).to_smt2_string());
  }
  fmt::println("(check-sat)");
  fmt::println("(exit)");
}
#endif

void TheorySolver::BoundsToTheoryRows(const Variable &var, BoundViolationType type, std::set<int> &theory_rows) const {
  if (type == BoundViolationType::NO_BOUND_VIOLATION) return;
  auto it = preprocessor_.theory_bounds().find(var);
  if (it == preprocessor_.theory_bounds().end()) return;
  const BoundVector &bound = it->second;
  return BoundsToTheoryRows(
      var, type == BoundViolationType::LOWER_BOUND_VIOLATION ? bound.active_lower_bound() : bound.active_upper_bound(),
      theory_rows);
}
void TheorySolver::BoundsToTheoryRows(const Variable &var, const mpq_class &value, std::set<int> &theory_rows) const {
  auto bound_it = preprocessor_.theory_bounds().find(var);
  if (bound_it == preprocessor_.theory_bounds().end()) return;
  const BoundVector &bound = bound_it->second;
  for (auto it = bound.GetActiveBound(value); it; ++it) {
    theory_rows.insert(lit_to_theory_row_.at(it->theory_literal.var.get_id()));
    for (const Literal &exp : it->explanation) theory_rows.insert(lit_to_theory_row_.at(exp.var.get_id()));
  }
}
SatResult TheorySolver::CheckSat(const Box &box, mpq_class *actual_precision, std::set<LiteralSet> &explanations) {
  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();

  DLINEAR_TRACE_FMT("TheorySolver::CheckSat: Box = \n{}", box);
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before CheckSat");

  model_ = box;
  DLINEAR_ASSERT(std::all_of(theory_col_to_var_.begin(), theory_col_to_var_.end(),
                             [&box](const Variable &var) { return box.has_variable(var); }),
                 "All theory variables must be present in the box");

  // If we can immediately return SAT afterward
  if (theory_row_to_lit_.empty()) {
    DLINEAR_DEBUG("TheorySolver::CheckSat: no need to call LP solver");
    UpdateModelBounds();
    return SatResult::SAT_SATISFIABLE;
  }

  if (config_.actual_bound_propagation_frequency() == Config::PreprocessingRunningFrequency::ALWAYS ||
      config_.actual_bound_propagation_frequency() == Config::PreprocessingRunningFrequency::ON_ITERATION) {
    timer_guard.pause();  // Pause the timer to measure the time spent in the preprocessor
    preprocessor_.Process(explanations);
    timer_guard.resume();
    DLINEAR_DEBUG("TheorySolver::CheckSat: conflict detected in preprocessing");
    if (!explanations.empty()) return SatResult::SAT_UNSATISFIABLE;
  }

  DLINEAR_DEV_DEBUG_FMT("TheorySolver::CheckSat: running {}", config_.lp_solver());
  return CheckSatCore(actual_precision, explanations);
}

}  // namespace dlinear
