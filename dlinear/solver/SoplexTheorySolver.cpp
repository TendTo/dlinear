/**
 * @file SoplexTheorySolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "SoplexTheorySolver.h"

#include <utility>

#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

using soplex::Rational;

mpq_class SoplexTheorySolver::infinity_{0};
mpq_class SoplexTheorySolver::ninfinity_{0};

SoplexTheorySolver::SoplexTheorySolver(PredicateAbstractor &predicate_abstractor, const Config &config)
    : TheorySolver(predicate_abstractor, config) {
  // Initialize infinities
  infinity_ = soplex::infinity;
  ninfinity_ = -soplex::infinity;
  // Default SoPlex parameters
  spx_.setRealParam(soplex::SoPlex::FEASTOL, config.precision());
  spx_.setBoolParam(soplex::SoPlex::RATREC, false);
  spx_.setIntParam(soplex::SoPlex::READMODE, soplex::SoPlex::READMODE_RATIONAL);
  spx_.setIntParam(soplex::SoPlex::SOLVEMODE, soplex::SoPlex::SOLVEMODE_RATIONAL);
  spx_.setIntParam(soplex::SoPlex::CHECKMODE, soplex::SoPlex::CHECKMODE_RATIONAL);
  spx_.setIntParam(soplex::SoPlex::SYNCMODE, soplex::SoPlex::SYNCMODE_AUTO);
  spx_.setIntParam(soplex::SoPlex::SIMPLIFIER, soplex::SoPlex::SIMPLIFIER_INTERNAL);
  spx_.setIntParam(soplex::SoPlex::VERBOSITY, config.verbose_simplex());
  // Default is maximize.
  spx_.setIntParam(soplex::SoPlex::OBJSENSE, soplex::SoPlex::OBJSENSE_MAXIMIZE);
  // Enable precision boosting
  bool enable_precision_boosting = config.lp_mode() != Config::LPMode::PURE_ITERATIVE_REFINEMENT;
  spx_.setBoolParam(soplex::SoPlex::ADAPT_TOLS_TO_MULTIPRECISION, enable_precision_boosting);
  spx_.setBoolParam(soplex::SoPlex::PRECISION_BOOSTING, enable_precision_boosting);
  spx_.setIntParam(soplex::SoPlex::RATFAC_MINSTALLS, enable_precision_boosting ? 0 : 2);
  // Enable iterative refinement
  bool enable_iterative_refinement = config.lp_mode() != Config::LPMode::PURE_PRECISION_BOOSTING;
  spx_.setBoolParam(soplex::SoPlex::ITERATIVE_REFINEMENT, enable_iterative_refinement);
  DLINEAR_DEBUG_FMT(
      "SoplexTheorySolver::SoplexTheorySolver: precision = {}, precision_boosting = {}, iterative_refinement = {}",
      config.precision(), enable_precision_boosting, enable_iterative_refinement);
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
  theory_bounds_.emplace_back(-soplex::infinity, soplex::infinity);
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
  DLINEAR_WARN_FMT("row: {}, row_value: {}, lhs: {}, rhs: {}", spx_row, row_value, lp_row.lhs(), lp_row.rhs());
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
  DLINEAR_WARN_FMT("row: {}, row_value: {}, lhs: {}, rhs: {}", spx_row, row_value, lp_row.lhs(), lp_row.rhs());
  return lp_row.lhs() == row_value || lp_row.rhs() == row_value;
}

soplex::DSVectorRational SoplexTheorySolver::ParseRowCoeff(const Formula &formula) {
  Expression expr{(get_lhs_expression(formula) - get_rhs_expression(formula))};
  if (needs_expansion_) expr = expr.Expand();
  DLINEAR_ASSERT(expr == expr.Expand(), "The expression must be expanded");

  soplex::DSVectorRational coeffs;
  spx_rhs_.emplace_back(0);

  if (is_constant(expr)) {
    spx_rhs_.back() = -get_constant_value(expr);
  } else if (is_variable(expr)) {
    SetSPXVarCoeff(coeffs, get_variable(expr), 1);
  } else if (is_multiplication(expr)) {
    std::map<Expression, Expression> map = get_base_to_exponent_map_in_multiplication(expr);
    if (map.size() != 1 || !is_variable(map.begin()->first) || !is_constant(map.begin()->second) ||
        get_constant_value(map.begin()->second) != 1) {
      DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", expr);
    }
    SetSPXVarCoeff(coeffs, get_variable(map.begin()->first), get_constant_in_multiplication(expr));
  } else if (is_addition(expr)) {
    const std::map<Expression, mpq_class> &map = get_expr_to_coeff_map_in_addition(expr);
    coeffs.setMax(static_cast<int>(map.size()));
    for (const auto &[var, coeff] : map) {
      if (!is_variable(var)) {
        DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", expr);
      }
      SetSPXVarCoeff(coeffs, get_variable(var), coeff);
    }
    spx_rhs_.back() = -get_constant_in_addition(expr);
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", expr);
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
  throw std::runtime_error("Not implemented");
  DLINEAR_ASSERT(2 == simplex_sat_phase_, "must be phase 2");
  const int spx_cols{spx_.numColsRational()};
  spx_lower_.reDim(spx_cols + 2, true);  // Set lower bounds to zero
  spx_upper_.reDim(spx_cols + 2, false);
  spx_upper_[spx_cols] = soplex::infinity;  // Set upper bounds to infinity
  spx_upper_[spx_cols + 1] = soplex::infinity;
  soplex::DSVectorRational coeffsPos;
  coeffsPos.add(spx_row, 1);
  spx_.addColRational(soplex::LPColRational(1, coeffsPos, soplex::infinity, 0));
  soplex::DSVectorRational coeffsNeg;
  coeffsNeg.add(spx_row, -1);
  spx_.addColRational(soplex::LPColRational(1, coeffsNeg, soplex::infinity, 0));
  DLINEAR_DEBUG_FMT("SoplexTheorySolver::CreateArtificials({} -> ({}, {}))", spx_row, spx_cols, spx_cols + 1);
}

void SoplexTheorySolver::Reset(const Box &box) {
  DLINEAR_TRACE_FMT("SoplexTheorySolver::Reset(): Box =\n{}", box);
  Consolidate();
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before resetting it");
  // Omitting to do this seems to cause problems in soplex
  spx_.clearBasis();
  for (auto &bound : theory_bounds_) bound.Clear();

  // Clear constraint bounds
  const int spx_rows = spx_.numRowsRational();
  DLINEAR_ASSERT(static_cast<size_t>(spx_rows) == theory_row_to_lit_.size(),
                 "spx_rows must be == from_spx_row_.size()");
  for (int i = 0; i < spx_rows; i++) spx_.changeRangeRational(i, -soplex::infinity, soplex::infinity);

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
                               const auto &[lb, ub] = theory_bounds_[theory_col].active_bound_value();
                               return lb <= ub;
                             }),
                 "All lower bounds must be <= upper bounds");

  // Update the box with the new bounds, since the LP solver won't be called, for there are no constraints.
  for (int theory_col = 0; theory_col < static_cast<int>(theory_col_to_var_.size()); theory_col++) {
    const Variable &var{theory_col_to_var_[theory_col]};
    const auto &[lb, ub] = theory_bounds_[theory_col].active_bound_value();
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
  const int rowcount = spx_.numRowsRational();
  soplex::VectorRational ray;
  ray.reDim(rowcount);
  // Get the Farkas ray to identify which rows are responsible for the conflict
  [[maybe_unused]] bool res = spx_.getDualFarkasRational(ray);
  DLINEAR_ASSERT(res, "getDualFarkasRational() must return true");
  explanation.clear();
  // For each row in the ray
  for (int i = 0; i < rowcount; ++i) {
    if (ray[i] == 0) continue;  // The row did not participate in the conflict, ignore it
    DLINEAR_TRACE_FMT("SoplexTheorySolver::UpdateExplanation: ray[{}] = {}", i, ray[i]);
    const auto &[var, truth] = theory_row_to_lit_[i];
    // Insert the conflicting row literal to the explanation. Use the latest truth value from the SAT solver
    explanation.emplace(var, truth);
    // Add all the active bounds for the free variables in the row to the explanation
    for (const auto &col_var : predicate_abstractor_[var].GetFreeVariables()) {
      const int theory_col = var_to_theory_col_.at(col_var.get_id());
      // TODO: get the value of the column from the ray for a smaller violation
      TheoryBoundsToExplanation(theory_col, true, explanation);
    }
  }
}

// bool SoplexTheorySolver::SetSPXVarBound(const TheorySolver::Bound &bound, int spx_col) {
//   const auto &[var, type, value] = bound;
//   return SetSPXVarBound(var, type, value, spx_col);
// }

void SoplexTheorySolver::SetSPXVarBound() {
  spx_upper_.reDim(spx_.numColsRational(), false);
  spx_lower_.reDim(spx_.numColsRational(), false);
  for (int theory_col = 0; theory_col < static_cast<int>(theory_bounds_.size()); theory_col++) {
    spx_lower_[theory_col] = theory_bounds_[theory_col].active_lower_bound().get_mpq_t();
    spx_upper_[theory_col] = theory_bounds_[theory_col].active_upper_bound().get_mpq_t();
  }
  spx_.changeLowerRational(spx_lower_);
  spx_.changeUpperRational(spx_upper_);
}

void SoplexTheorySolver::SetSpxRow(const int spx_row) {
  const auto &[var, truth] = theory_row_to_lit_[spx_row];
  SetSpxRow(spx_row, truth, predicate_abstractor_[var].GetFreeVariables());
}
void SoplexTheorySolver::SetSpxRow(const int spx_row, const bool truth) {
  SetSpxRow(spx_row, truth, predicate_abstractor_[theory_row_to_lit_[spx_row].first].GetFreeVariables());
}
void SoplexTheorySolver::SetSpxRow(int spx_row, const Variables &free_vars) {
  SetSpxRow(spx_row, theory_row_to_lit_[spx_row].second, free_vars);
}

}  // namespace dlinear
