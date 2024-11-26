/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "LpTheorySolver.h"

#include <algorithm>
#include <cstddef>
#include <map>
#include <utility>

#include "dlinear/solver/theory_solver/qf_lra/EqBinomialBoundPreprocessor.h"
#include "dlinear/solver/theory_solver/qf_lra/SimpleBoundPropagator.h"
#include "dlinear/util/error.h"
#include "dlinear/util/logging.h"

namespace dlinear {

LpTheorySolver::LpTheorySolver(const PredicateAbstractor &predicate_abstractor, const std::string &class_name)
    : QfLraTheorySolver{predicate_abstractor, class_name}, lp_solver_{LpSolver::GetInstance(config_)} {
  auto env{std::make_shared<Environment>()};
  auto var_bounds{std::make_shared<BoundVectorMap>()};

  // Propagators
  if (config_.actual_simple_bound_propagation_step() != Config::ExecutionStep::NEVER)
    AddPropagator(std::make_unique<SimpleBoundPropagator>(*this));

  // Preprocessors
  if (config_.actual_eq_binomial_bound_preprocess_step() != Config::ExecutionStep::NEVER)
    AddPreprocessor(std::make_unique<EqBinomialBoundPreprocessor>(*this, var_bounds, env, class_name));
}

void LpTheorySolver::AddLiterals() {
  DLINEAR_ASSERT(!is_consolidated_, "Cannot add literals after consolidation");
  lp_solver_->ReserveRows(static_cast<int>(pa_.var_to_formula_map().size()));
  lp_solver_->ReserveColumns(static_cast<int>(pa_.var_to_formula_map().size()));
  TheorySolver::AddLiterals();
}
void LpTheorySolver::AddLiterals(std::span<const Literal> literals) {
  DLINEAR_ASSERT(!is_consolidated_, "Cannot add literals after consolidation");
  lp_solver_->ReserveRows(static_cast<int>(literals.size()));
  lp_solver_->ReserveColumns(static_cast<int>(literals.size()));
  TheorySolver::AddLiterals(literals);
}

void LpTheorySolver::AddVariable(const Variable &var) {
  DLINEAR_ASSERT(!is_consolidated_, "Cannot add variables after consolidation");
  if (lp_solver_->var_to_col().contains(var)) return;  // Variable is already present
  lp_solver_->AddColumn(var);
  vars_bounds_.emplace(var, BoundVector{lp_solver_->ninfinity(), lp_solver_->infinity()});
  for (const std::unique_ptr<TheoryPreprocessor> &preprocessor : preprocessors_) preprocessor->AddVariable(var);
  DLINEAR_DEBUG_FMT("LpTheorySolver::AddVariable({} ↦ {})", var, lp_solver_->num_columns());
}

void LpTheorySolver::Consolidate(const Box &box) {
  if (is_consolidated_) return;

  lp_solver_->Consolidate();
  rows_state_.resize(lp_solver_->num_rows(), false);

  DLINEAR_ASSERT(static_cast<int>(lp_solver_->col_to_var().size()) <= lp_solver_->num_columns(),
                 "theory_col must be in bounds");
  // Set variable bounds based on the box
  for (const Variable &var : lp_solver_->col_to_var()) {
    if (box.has_variable(var)) {
      DLINEAR_ASSERT_FMT(lp_solver_->ninfinity() <= box[var].lb(), "invalid lower bound. Expected {} <= {}",
                         lp_solver_->ninfinity(), box[var].lb());
      DLINEAR_ASSERT_FMT(box[var].lb() <= box[var].ub(), "invalid bounds. Expected {} <= {}", box[var].lb(),
                         box[var].ub());
      DLINEAR_ASSERT_FMT(box[var].ub() <= lp_solver_->infinity(), "invalid upper bound. Expected {} <= {}",
                         box[var].ub(), lp_solver_->infinity());
      vars_bounds_.insert_or_assign(var, BoundVector{box[var].lb(), box[var].ub()});
    }
  }

  // Backtrack preprocessor to the fixed bounds
  //  if (preprocessor_ != nullptr) preprocessor_->Backtrack();
  TheorySolver::Consolidate(box);
}

void LpTheorySolver::CreateCheckpoint() {
  for (auto &[var, bounds] : vars_bounds_) vars_bounds_checkpoint_.insert_or_assign(var, bounds);
  rows_state_checkpoint_ = rows_state_;
  DLINEAR_DEBUG_FMT("LpTheorySolver::CreateCheckpoint: #var_bounds = {}, #rows_state = {}",
                    vars_bounds_checkpoint_.size(), rows_state_checkpoint_.size());
  DLINEAR_TRACE_FMT("LpTheorySolver::CreateCheckpoint: var_bounds = {}, rows_state = {}", vars_bounds_checkpoint_,
                    rows_state_checkpoint_);
}

void LpTheorySolver::Backtrack() {
  TheorySolver::Backtrack();
  // Disable all rows
  lp_solver_->Backtrack();
  rows_state_ = rows_state_checkpoint_;
  for (auto &[var, bounds] : vars_bounds_) bounds = vars_bounds_checkpoint_.at(var);
}

void LpTheorySolver::UpdateModelSolution() {
  DLINEAR_ASSERT(!lp_solver_->solution().empty(), "solution must be available");
  DLINEAR_ASSERT(lp_solver_->solution().size() >= lp_solver_->col_to_var().size(),
                 "solution must contain all the variables");

  DLINEAR_TRACE("LpTheorySolver::UpdateModelSolution()");
  for (int theory_col = 0; theory_col < static_cast<int>(lp_solver_->col_to_var().size()); theory_col++) {
    const Variable &var = lp_solver_->col_to_var().at(theory_col);
    const mpq_class &val = lp_solver_->solution().at(theory_col);
    DLINEAR_ASSERT(model_[var].lb() <= val && val <= model_[var].ub(), "val must be in bounds");
    model_[var] = val;
  }
}

void LpTheorySolver::UpdateModelBounds() {
  DLINEAR_ASSERT(lp_solver_->num_rows() == 0, "There must be no rows in the LP solver");
  DLINEAR_ASSERT(std::all_of(lp_solver_->col_to_var().cbegin(), lp_solver_->col_to_var().cend(),
                             [this](const Variable &var) {
                               const auto &[lb, ub] = vars_bounds_.at(var).GetActiveBoundsValue();
                               return lb <= ub;
                             }),
                 "All lower bounds must be <= upper bounds");

  // Update the box with the new bounds, since the LP solver won't be called, for there are no constraints.
  for (const auto &[var, bounds] : vars_bounds_) {
    const auto &[lb, ub] = bounds.GetActiveBoundsValue();
    model_[var] = Interval{std::max(model_[var].lb(), lb), std::min(ub, model_[var].ub())};
  }
}

void LpTheorySolver::NotifyInfeasible(const ConflictCallback &conflict_cb) const {
  DLINEAR_ASSERT(!lp_solver_->infeasible_rows().empty(), "There must be infeasible rows");
  LiteralSet explanation;
  for (const auto &row : lp_solver_->infeasible_rows()) {
    explanation.insert(lp_solver_->row_to_lit().at(row));
  }
  for (const auto &[column, upper_bound] : lp_solver_->infeasible_bounds()) {
    const Variable &var = lp_solver_->col_to_var().at(column);
    const BoundVector &var_bounds = vars_bounds_.at(var);
    var_bounds.GetActiveBounds(upper_bound ? var_bounds.active_upper_bound() : var_bounds.active_lower_bound())
        .explanation(explanation);
  }
  conflict_cb(explanation);
}

void LpTheorySolver::DisableNotEnabledRows() {
  for (int row = 0; row < static_cast<int>(rows_state_.size()); row++) {
    if (!rows_state_.at(row)) lp_solver_->DisableRow(row);
  }
}

void LpTheorySolver::EnableVarBound() {
  for (const auto &[var, bounds] : vars_bounds_) {
    lp_solver_->EnableBound(lp_solver_->var_to_col().at(var), bounds.active_lower_bound(), bounds.active_upper_bound());
    DLINEAR_TRACE_FMT(
        "EnableVarBound: {} = [{}, {}]", var,
        bounds.active_lower_bound() <= lp_solver_->ninfinity() ? "-inf" : fmt::to_string(bounds.active_lower_bound()),
        bounds.active_upper_bound() >= lp_solver_->infinity() ? "inf" : fmt::to_string(bounds.active_upper_bound()));
  }
}

LiteralSet LpTheorySolver::enabled_literals() const {
  std::set<Literal> enabled_lits{};
  for (std::size_t i = 0; i < lp_solver_->row_to_lit().size(); ++i) {
    if (rows_state_[i]) enabled_lits.insert(lp_solver_->row_to_lit().at(i));
  }
  for (const auto &[var, bound] : vars_bounds_) {
    const BoundIterator it = bound.GetActiveBounds();
    it.explanation(enabled_lits);
  }
  return enabled_lits;
}

}  // namespace dlinear
