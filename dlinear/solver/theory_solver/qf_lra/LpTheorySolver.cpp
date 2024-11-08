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

#include "dlinear/util/Config.h"
#include "dlinear/util/error.h"
#include "dlinear/util/logging.h"

namespace dlinear {

LpTheorySolver::LpTheorySolver(PredicateAbstractor &predicate_abstractor, const std::string &class_name)
    : QfLraTheorySolver{predicate_abstractor, class_name} {}

void LpTheorySolver::AddLiterals() {
  const int num_literals = static_cast<int>(pa_.var_to_formula_map().size());
  TheorySolver::AddLiterals();
}

void LpTheorySolver::AddVariable(const Variable &var) {
  DLINEAR_ASSERT(!is_consolidated_, "Cannot add variables after consolidation");
  auto it = var_to_lp_col_.find(var);
  // The variable is already present
  if (it != var_to_lp_col_.end()) return;

  const int num_cols = lp_solver_->num_columns();
  lp_solver_->AddColumn();
  var_to_lp_col_.emplace(var, num_cols);
  lp_col_to_var_.emplace_back(var);
  if (preprocessor_ != nullptr) preprocessor_->AddVariable(var);
  DLINEAR_DEBUG_FMT("LpTheorySolver::AddVariable({} ↦ {})", var, num_cols);
}

void LpTheorySolver::Consolidate(const Box &box) {
  if (is_consolidated_) return;

  lp_solver_->Consolidate();

  DLINEAR_ASSERT(static_cast<int>(lp_col_to_var_.size()) <= lp_solver_->num_columns(), "theory_col must be in bounds");
  // Set variable bounds based on the box
  for (const Variable &var : lp_col_to_var_) {
    if (box.has_variable(var)) {
      DLINEAR_ASSERT(lp_solver_->ninfinity() <= box[var].lb(), "lower bound must be >= -infinity");
      DLINEAR_ASSERT(box[var].lb() <= box[var].ub(), "lower bound must be <= upper bound");
      DLINEAR_ASSERT(box[var].ub() <= lp_solver_->infinity(), "upper bound must be <= infinity");
      preprocessor_->SetInfinityBounds(var, box[var].lb(), box[var].ub());
    }
  }

  // Backtrack preprocessor to the fixed bounds
  preprocessor_->Clear(fixed_preprocessor_);
  TheorySolver::Consolidate(box);
}

void LpTheorySolver::Backtrack() {
  TheorySolver::Backtrack();
  lp_solver_->Backtrack();
}

void LpTheorySolver::UpdateModelSolution() {
  DLINEAR_TRACE("LpTheorySolver::UpdateModelSolution()");
  DLINEAR_ASSERT(lp_solver_->solution().has_value(), "solution must be available");
  DLINEAR_ASSERT(lp_solver_->solution().value().size() >= lp_col_to_var_.size(),
                 "solution must contain all the variables");
  for (int theory_col = 0; theory_col < static_cast<int>(lp_col_to_var_.size()); theory_col++) {
    const Variable &var{lp_col_to_var_[theory_col]};
    const mpq_class val = lp_solver_->solution().value().at(theory_col);
    DLINEAR_ASSERT(model_[var].lb() <= val && val <= model_[var].ub(), "val must be in bounds");
    model_[var] = val;
  }
}

void LpTheorySolver::UpdateModelBounds() {
  DLINEAR_ASSERT(lp_solver_->num_rows() == 0, "There must be no rows in the LP solver");
  DLINEAR_ASSERT(std::all_of(lp_col_to_var_.cbegin(), lp_col_to_var_.cend(),
                             [this](const Variable &var) {
                               const auto &[lb, ub] = vars_bounds_.at(var).GetActiveBoundsValue();
                               return lb <= ub;
                             }),
                 "All lower bounds must be <= upper bounds");

  // Update the box with the new bounds, since the LP solver won't be called, for there are no constraints.
  for (const auto &[var, bounds] : vars_bounds_) {
    const auto &[lb, ub] = bounds.GetActiveBoundsValue();
    mpq_class val;
    if (lp_solver_->ninfinity() < lb) {
      val = lb;
    } else if (ub < lp_solver_->infinity()) {
      val = ub;
    } else {
      val = 0;
    }
    DLINEAR_ASSERT(model_[var].lb() <= val && val <= model_[var].ub(), "val must be in bounds");
    model_[var] = val;
  }
}

void LpTheorySolver::UpdateExplanation(LiteralSet &explanation) {
  explanation.clear();
  for (const auto &bound : lp_solver_->infeasible_bounds().value()) {
    const Variable &var = lp_col_to_var_[std::abs(bound)];
    const BoundVector &var_bounds = vars_bounds_.at(var);
    var_bounds.GetActiveBounds(bound < 0 ? var_bounds.active_lower_bound() : var_bounds.active_upper_bound())
        .explanation(explanation);
  }
  for (const auto &row : lp_solver_->infeasible_rows().value()) {
    explanation.insert(lp_row_to_lit_[row]);
  }
}

void LpTheorySolver::DisableNotEnabledRows() {
  for (int theory_row = 0; theory_row < lp_solver_->num_rows(); theory_row++) {
    if (!lp_rows_state_.at(theory_row)) lp_solver_->DisableRow(theory_row);
  }
}

void LpTheorySolver::EnableSpxVarBound() {
  for (const auto &[var, bounds] : vars_bounds_) {
    lp_solver_->EnableBound(var_to_lp_col_.at(var), bounds.active_lower_bound(), bounds.active_upper_bound());
    DLINEAR_TRACE_FMT("EnableSpxVarBound: {} = [{}, {}]", var, bounds.active_lower_bound(),
                      bounds.active_upper_bound());
  }
}

void LpTheorySolver::EnableSpxRow(const int spx_row) {
  const auto &[var, truth] = lp_row_to_lit_[spx_row];
  EnableSpxRow(spx_row, truth);
}

}  // namespace dlinear
