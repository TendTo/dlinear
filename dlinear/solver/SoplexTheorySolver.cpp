/**
 * @file SoplexTheorySolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "SoplexTheorySolver.h"

#include <algorithm>
#include <cstddef>
#include <map>
#include <utility>

#include "dlinear/solver/TheorySolverBoundPreprocessor.h"
#include "dlinear/solver/TheorySolverBoundVector.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

using soplex::Rational;

const mpq_class SoplexTheorySolver::infinity_{soplex::infinity};
const mpq_class SoplexTheorySolver::ninfinity_{-soplex::infinity};

SoplexTheorySolver::SoplexTheorySolver(PredicateAbstractor &predicate_abstractor, const std::string &class_name)
    : TheorySolver(predicate_abstractor, class_name) {
  // Default SoPlex parameters
  spx_.setRealParam(soplex::SoPlex::FEASTOL, config_.precision());
  spx_.setBoolParam(soplex::SoPlex::RATREC, false);
  spx_.setIntParam(soplex::SoPlex::READMODE, soplex::SoPlex::READMODE_RATIONAL);
  spx_.setIntParam(soplex::SoPlex::SOLVEMODE, soplex::SoPlex::SOLVEMODE_RATIONAL);
  spx_.setIntParam(soplex::SoPlex::CHECKMODE, soplex::SoPlex::CHECKMODE_RATIONAL);
  spx_.setIntParam(soplex::SoPlex::SYNCMODE, soplex::SoPlex::SYNCMODE_AUTO);
  spx_.setIntParam(soplex::SoPlex::SIMPLIFIER, soplex::SoPlex::SIMPLIFIER_INTERNAL);
  spx_.setIntParam(soplex::SoPlex::VERBOSITY, config_.verbose_simplex());
  // Default is maximize.
  spx_.setIntParam(soplex::SoPlex::OBJSENSE, soplex::SoPlex::OBJSENSE_MAXIMIZE);
  // Enable precision boosting
  bool enable_precision_boosting = config_.lp_mode() != Config::LPMode::PURE_ITERATIVE_REFINEMENT;
  spx_.setBoolParam(soplex::SoPlex::ADAPT_TOLS_TO_MULTIPRECISION, enable_precision_boosting);
  spx_.setBoolParam(soplex::SoPlex::PRECISION_BOOSTING, enable_precision_boosting);
  spx_.setIntParam(soplex::SoPlex::RATFAC_MINSTALLS, enable_precision_boosting ? 0 : 2);
  // Enable iterative refinement
  bool enable_iterative_refinement = config_.lp_mode() != Config::LPMode::PURE_PRECISION_BOOSTING;
  spx_.setBoolParam(soplex::SoPlex::ITERATIVE_REFINEMENT, enable_iterative_refinement);
  DLINEAR_DEBUG_FMT(
      "SoplexTheorySolver::SoplexTheorySolver: precision = {}, precision_boosting = {}, iterative_refinement = {}",
      config_.precision(), enable_precision_boosting, enable_iterative_refinement);
}

void SoplexTheorySolver::AddVariable(const Variable &var) {
  auto it = var_to_theory_col_.find(var.get_id());
  // The variable is already present
  if (it != var_to_theory_col_.end()) return;

  const int spx_col{spx_.numColsRational()};
  // obj, coeffs, upper, lower
  spx_.addColRational(soplex::LPColRational(0, soplex::DSVectorRational(), soplex::infinity, -soplex::infinity));
  var_to_theory_col_.emplace(var.get_id(), spx_col);
  theory_col_to_var_.emplace_back(var);
  theory_bounds_.emplace_back(ninfinity_, infinity_);
  DLINEAR_DEBUG_FMT("SoplexTheorySolver::AddVariable({} ↦ {})", var, spx_col);
}

std::vector<std::pair<int, Rational>> SoplexTheorySolver::GetActiveRows() {
  std::vector<std::pair<int, Rational>> active_rows;
  soplex::VectorRational row_values{spx_.numRowsRational()};
  soplex::LPRowSetRational lp_rows;
  [[maybe_unused]] const bool res = spx_.getRowsActivityRational(row_values);
  DLINEAR_ASSERT(res, "The problem must have a solution");
  DLINEAR_TRACE_FMT("SoplexTheorySolver::GetActiveRows: row_values = {}", row_values);
  spx_.getRowsRational(0, spx_.numRowsRational() - 1, lp_rows);
  for (int i = 0; i < lp_rows.num(); i++) {
    if (lp_rows.lhs(i) == row_values[i] || lp_rows.rhs(i) == row_values[i]) active_rows.emplace_back(i, row_values[i]);
  }
  return active_rows;
}

std::vector<std::pair<int, soplex::Rational>> SoplexTheorySolver::GetActiveRows(const std::vector<int> &spx_rows) {
  std::vector<std::pair<int, Rational>> active_rows;
  soplex::VectorRational row_values{spx_.numRowsRational()};
  soplex::LPRowSetRational lp_rows;
  [[maybe_unused]] const bool res = spx_.getRowsActivityRational(spx_rows, row_values);
  DLINEAR_TRACE_FMT("SoplexTheorySolver::GetActiveRows: row_values = {} in {} rows", row_values, spx_rows.size());
  DLINEAR_ASSERT(res, "The problem must have a solution");
  spx_.getRowsRational(0, spx_.numRowsRational() - 1, lp_rows);
  for (const int i : spx_rows) {
    if (lp_rows.lhs(i) == row_values[i] || lp_rows.rhs(i) == row_values[i]) active_rows.emplace_back(i, row_values[i]);
  }
  return active_rows;
}

std::optional<Rational> SoplexTheorySolver::IsRowActive(const int spx_row) {
  Rational row_value;
  soplex::LPRowRational lp_row;
  [[maybe_unused]] const bool res = spx_.getRowActivityRational(spx_row, row_value);
  DLINEAR_ASSERT(res, "The problem must have a solution and the row must be present");
  spx_.getRowRational(spx_row, lp_row);
  DLINEAR_TRACE_FMT("SoplexTheorySolver::IsRowActive: {} =? {} =? {}", lp_row.lhs(), row_value, lp_row.rhs());
  return lp_row.lhs() == row_value || lp_row.rhs() == row_value ? std::optional{std::move(row_value)}
                                                                : std::optional<Rational>{};
}

bool SoplexTheorySolver::IsRowActive(const int spx_row, const Rational &value) {
  Rational row_value;
  soplex::LPRowRational lp_row;
  [[maybe_unused]] const bool res = spx_.getRowActivityRational(spx_row, row_value);
  DLINEAR_ASSERT(res, "The problem must have a solution and the row must be present");
  if (row_value != value) return false;
  spx_.getRowRational(spx_row, lp_row);
  DLINEAR_TRACE_FMT("SoplexTheorySolver::IsRowActive: {} =? {} =? {}", lp_row.lhs(), row_value, lp_row.rhs());
  return lp_row.lhs() == row_value || lp_row.rhs() == row_value;
}

soplex::DSVectorRational SoplexTheorySolver::ParseRowCoeff(const Formula &formula) {
  DLINEAR_ASSERT_FMT(formula.IsFlattened(), "The formula {} must be flattened", formula);
  // Add constraint to the preprocessor
  preprocessor_.AddConstraint(static_cast<int>(spx_rhs_.size()), formula);

  const Expression &lhs = get_lhs_expression(formula);
  const Expression &rhs = get_rhs_expression(formula);

  soplex::DSVectorRational coeffs;
  spx_rhs_.emplace_back(get_constant_value(rhs));

  if (is_variable(lhs)) {
    SetSPXVarCoeff(coeffs, get_variable(lhs), 1);
  } else if (is_addition(lhs)) {
    DLINEAR_ASSERT(get_constant_in_addition(lhs) == 0, "The addition constant must be 0");
    const std::map<Expression, mpq_class> &map = get_expr_to_coeff_map_in_addition(lhs);
    coeffs.setMax(static_cast<int>(map.size()));
    for (const auto &[var, coeff] : map) {
      if (!is_variable(var)) DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", lhs);
      SetSPXVarCoeff(coeffs, get_variable(var), coeff);
    }
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
  }
  if (spx_rhs_.back() <= -soplex::infinity || spx_rhs_.back() >= soplex::infinity) {
    DLINEAR_RUNTIME_ERROR_FMT("LP RHS value too large: {}", spx_rhs_.back());
  }
  return coeffs;
}

void SoplexTheorySolver::SetSPXVarCoeff(soplex::DSVectorRational &coeffs, const Variable &var,
                                        const mpq_class &value) const {
  const auto it = var_to_theory_col_.find(var.get_id());
  if (it == var_to_theory_col_.end()) DLINEAR_RUNTIME_ERROR_FMT("Variable undefined: {}", var);
  if (value <= -soplex::infinity || value >= soplex::infinity) {
    DLINEAR_RUNTIME_ERROR_FMT("LP coefficient too large: {}", value);
  }
  coeffs.add(it->second, gmp::to_mpq_t(value));
}

void SoplexTheorySolver::CreateArtificials(const int spx_row) {
  DLINEAR_RUNTIME_ERROR("Not implemented");
  DLINEAR_ASSERT(2 == config_.simplex_sat_phase(), "must be phase 2");
  [[maybe_unused]] const int spx_cols{spx_.numColsRational()};
  soplex::DSVectorRational coeffsPos;
  coeffsPos.add(spx_row, 1);
  spx_.addColRational(soplex::LPColRational(1, coeffsPos, soplex::infinity, 0));
  soplex::DSVectorRational coeffsNeg;
  coeffsNeg.add(spx_row, -1);
  spx_.addColRational(soplex::LPColRational(1, coeffsNeg, soplex::infinity, 0));
  DLINEAR_DEBUG_FMT("SoplexTheorySolver::CreateArtificials({} -> ({}, {}))", spx_row, spx_cols, spx_cols + 1);
}

void SoplexTheorySolver::GetSpxInfeasibilityRay(soplex::VectorRational &farkas_ray) {
  DLINEAR_ASSERT(farkas_ray.dim() == spx_.numRowsRational(), "farkas_ray must have the same dimension as the rows");
  // Get the Farkas ray to identify which rows are responsible for the conflict
  [[maybe_unused]] bool res = spx_.getDualFarkasRational(farkas_ray);
  DLINEAR_ASSERT(res, "getDualFarkasRational() must return true");
}

void SoplexTheorySolver::GetSpxInfeasibilityRay(soplex::VectorRational &farkas_ray,
                                                std::vector<BoundViolationType> &bounds_ray) {
  GetSpxInfeasibilityRay(farkas_ray);

  DLINEAR_ASSERT(static_cast<int>(bounds_ray.size()) == spx_.numColsRational() - 1,
                 "bounds_ray must have the same dimension as the cols");
  DLINEAR_ASSERT(std::all_of(bounds_ray.cbegin(), bounds_ray.cend(),
                             [](const BoundViolationType &it) { return it == BoundViolationType::NO_BOUND_VIOLATION; }),
                 "bounds_ray must be initialized to NO_BOUND_VIOLATION");
  //  Multiply the Farkas ray by the row coefficients to get the column violations: ray * A
  //  If the result is non-zero, the sign indicates the bound that caused the violation.
  Rational col_violation{0};
  for (int i = 0; i < spx_.numColsRational() - 1; i++) {
    col_violation = 0;
    for (int j = 0; j < spx_.numRowsRational(); j++) {
      col_violation += farkas_ray[j] * spx_.rowVectorRational(j)[i];
    }
    if (col_violation.is_zero()) continue;
    DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::UpdateExplanationInfeasible: {}[{}] = {}", theory_col_to_var_[i], i,
                      col_violation);
    bounds_ray[i] =
        col_violation > 0 ? BoundViolationType::LOWER_BOUND_VIOLATION : BoundViolationType::UPPER_BOUND_VIOLATION;
  }
}

void SoplexTheorySolver::Reset(const Box &box) {
  DLINEAR_TRACE_FMT("SoplexTheorySolver::Reset(): Box =\n{}", box);
  Consolidate();
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before resetting it");

  // Omitting to do this seems to cause problems in soplex
  // https://github.com/scipopt/soplex/issues/38
  spx_.clearBasis();
  // Clear the preprocessor
  preprocessor_.Clear();
  // Clear enabled theory rows
  enabled_theory_rows_.clear();

  // Clear constraint bounds
  for (auto &bound : theory_bounds_) bound.Clear();
  const int spx_rows = spx_.numRowsRational();
  DLINEAR_ASSERT(static_cast<std::size_t>(spx_rows) == theory_row_to_lit_.size(), "Row count mismatch");
  theory_rows_state_.assign(spx_rows, false);

  // Clear variable bounds
  [[maybe_unused]] const int spx_cols{spx_.numColsRational()};
  for (int theory_col = 0; theory_col < static_cast<int>(theory_col_to_var_.size()); theory_col++) {
    const Variable &var{theory_col_to_var_[theory_col]};
    DLINEAR_ASSERT(0 <= theory_col && theory_col < spx_cols, "theory_col must be in bounds");
    if (box.has_variable(var)) {
      DLINEAR_ASSERT(ninfinity_ <= box[var].lb(), "lower bound must be >= -infinity");
      DLINEAR_ASSERT(box[var].lb() <= box[var].ub(), "lower bound must be <= upper bound");
      DLINEAR_ASSERT(box[var].ub() <= infinity_, "upper bound must be <= infinity");
      theory_bounds_[theory_col].SetBounds(box[var].lb(), box[var].ub());
    }
    spx_.changeBoundsRational(theory_col, -soplex::infinity, soplex::infinity);
  }
}

void SoplexTheorySolver::UpdateModelBounds() {
  DLINEAR_ASSERT(spx_.numRowsRational() == 0, "There must be no rows in the LP solver");
  DLINEAR_ASSERT(std::all_of(theory_col_to_var_.cbegin(), theory_col_to_var_.cend(),
                             [this](const Variable &it) {
                               const int theory_col = &it - &theory_col_to_var_[0];
                               const auto &[lb, ub] = theory_bounds_[theory_col].GetActiveBoundsValue();
                               return lb <= ub;
                             }),
                 "All lower bounds must be <= upper bounds");

  // Update the box with the new bounds, since the LP solver won't be called, for there are no constraints.
  for (int theory_col = 0; theory_col < static_cast<int>(theory_col_to_var_.size()); theory_col++) {
    const Variable &var{theory_col_to_var_[theory_col]};
    const auto &[lb, ub] = theory_bounds_[theory_col].GetActiveBoundsValue();
    mpq_class val;
    if (-soplex::infinity < lb) {
      val = lb;
    } else if (ub < soplex::infinity) {
      val = ub;
    } else {
      val = 0;
    }
    DLINEAR_ASSERT(model_[var].lb() <= val && val <= model_[var].ub(), "val must be in bounds");
    model_[var] = val;
  }
}
void SoplexTheorySolver::UpdateExplanation(LiteralSet &explanation) {
  soplex::VectorRational ray{spx_.numRowsRational()};
  GetSpxInfeasibilityRay(ray);

  explanation.clear();
  // For each row in the ray
  for (int i = 0; i < spx_.numRowsRational(); ++i) {
    if (ray[i] == 0) continue;  // The row did not participate in the conflict, ignore it
    DLINEAR_TRACE_FMT("SoplexTheorySolver::UpdateExplanation: ray[{}] = {}", i, ray[i]);
    const auto &[var, truth] = theory_row_to_lit_[i];
    // Insert the conflicting row literal to the explanation. Use the latest truth value from the SAT solver
    explanation.emplace(var, truth);
    // Add all the active bounds for the free variables in the row to the explanation
    for (const auto &col_var : predicate_abstractor_[var].GetFreeVariables()) {
      const int theory_col = var_to_theory_col_.at(col_var.get_id());
      TheoryBoundsToExplanation(theory_col, explanation);
    }
  }
}

void SoplexTheorySolver::DisableSpxRows() {
  for (int theory_row = 0; theory_row < spx_.numRowsRational(); theory_row++) {
    if (!theory_rows_state_.at(theory_row)) spx_.changeRangeRational(theory_row, -soplex::infinity, soplex::infinity);
  }
}

void SoplexTheorySolver::EnableSPXVarBound() {
  for (int theory_col = 0; theory_col < static_cast<int>(theory_bounds_.size()); theory_col++) {
    spx_.changeBoundsRational(theory_col, theory_bounds_[theory_col].active_lower_bound().get_mpq_t(),
                              theory_bounds_[theory_col].active_upper_bound().get_mpq_t());
    if (theory_col == static_cast<int>(theory_bounds_.size() - 1)) continue;
    DLINEAR_TRACE_FMT("EnableSPXVarBound: {} = [{}, {}]", theory_col_to_var_[theory_col],
                      theory_bounds_[theory_col].active_lower_bound(), theory_bounds_[theory_col].active_upper_bound());
  }
  for (const auto &[var, value] : preprocessor_.env()) {
    const int theory_col = var_to_theory_col_.at(var.get_id());
    DLINEAR_TRACE_FMT("EnableSPXVarBound: {} = {} (theory_col: {})", var, value, theory_col);
    spx_.changeBoundsRational(theory_col, value.get_mpq_t(), value.get_mpq_t());
  }
}

void SoplexTheorySolver::EnableSpxRow(const int spx_row) {
  const auto &[var, truth] = theory_row_to_lit_[spx_row];
  EnableSpxRow(spx_row, truth);
}

}  // namespace dlinear
