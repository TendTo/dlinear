/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "SoplexLpSolver.h"

#include "dlinear/util/error.h"
#include "dlinear/util/logging.h"

namespace dlinear {

using soplex::Rational;
using SoplexStatus = soplex::SPxSolver::Status;

SoplexLpSolver::SoplexLpSolver(const Config& config, const std::string& class_name)
    : LpSolver{config, class_name},
      spx_{},
      ninfinity_{-soplex::infinity},
      infinity_{soplex::infinity},
      rninfinity_{-soplex::infinity},
      rinfinity_{soplex::infinity} {
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

int SoplexLpSolver::num_columns() const { return spx_cols_.num() > 0 ? spx_cols_.num() : spx_.numColsRational(); }
int SoplexLpSolver::num_rows() const { return spx_rows_.num() > 0 ? spx_rows_.num() : spx_.numRowsRational(); }
const mpq_class& SoplexLpSolver::ninfinity() const { return infinity_; }
const mpq_class& SoplexLpSolver::infinity() const { return ninfinity_; }

void SoplexLpSolver::ReserveColumns(const int num_columns) {
  LpSolver::ReserveColumns(num_columns);
  spx_cols_ = soplex::LPColSetRational(num_columns, num_columns);
}
void SoplexLpSolver::ReserveRows(const int num_rows) {
  LpSolver::ReserveRows(num_rows);
  spx_rows_ = soplex::LPRowSetRational(num_rows, num_rows);
}

void SoplexLpSolver::AddColumn() {
  // Add the column to the LP
  spx_cols_.add(soplex::LPColRational(0, soplex::DSVectorRational(), rinfinity_, rninfinity_));
}
void SoplexLpSolver::AddRow(const Formula& formula, LpRowSense sense) {
  senses_.emplace_back(sense);
  spx_rows_.add(soplex::LPRowRational(rninfinity_, ParseRowCoeff(formula), rinfinity_));
}
void SoplexLpSolver::SetObjective(int column, const mpq_class& value) {
  spx_.changeObjRational(column, Rational(value.get_mpq_t()));
}
void SoplexLpSolver::EnableRow(const int row, const LpRowSense sense, const mpq_class& rhs) {
  DLINEAR_ASSERT(row < num_rows(), "Row index out of bounds");
  DLINEAR_ASSERT(ninfinity_ <= rhs && rhs <= infinity_, "LP RHS value too large");
  if (sense == LpRowSense::NQ) {
    DisableRow(row);
    return;
  }

  spx_.changeRangeRational(
      row,
      sense == LpRowSense::GE || sense == LpRowSense::GT || sense == LpRowSense::EQ ? Rational(rhs.get_mpq_t())
                                                                                    : rninfinity_,
      sense == LpRowSense::LE || sense == LpRowSense::LT || sense == LpRowSense::EQ ? Rational(rhs.get_mpq_t())
                                                                                    : rinfinity_);
}
void SoplexLpSolver::EnableBound(const int column, const LpColBound bound, const mpq_class& value) {
  switch (bound) {
    case LpColBound::B:
      spx_.changeBoundsRational(column, Rational(value.get_mpq_t()), Rational(value.get_mpq_t()));
      break;
    case LpColBound::L:
    case LpColBound::SL:
      spx_.changeBoundsRational(column, Rational(value.get_mpq_t()), rinfinity_);
      break;
    case LpColBound::U:
    case LpColBound::SU:
      spx_.changeBoundsRational(column, rninfinity_, Rational(value.get_mpq_t()));
      break;
    case LpColBound::D:
    case LpColBound::F:
      DisableBound(column);
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
}
void SoplexLpSolver::EnableBound(const int column, const mpq_class& lb, const mpq_class& ub) {
  spx_.changeBoundsRational(column, Rational(lb.get_mpq_t()), Rational(ub.get_mpq_t()));
}
void SoplexLpSolver::DisableBound(const int column) { spx_.changeBoundsRational(column, rninfinity_, rinfinity_); }
void SoplexLpSolver::DisableRow(const int row) { spx_.changeRangeRational(row, rninfinity_, rinfinity_); }

void SoplexLpSolver::Consolidate() {
  spx_.addColsRational(spx_cols_);
  spx_.addRowsRational(spx_rows_);
}
void SoplexLpSolver::Backtrack() {
  LpSolver::Backtrack();
  // Omitting to do this seems to cause problems in soplex
  // https://github.com/scipopt/soplex/issues/38
  spx_.clearBasis();
}
LpResult SoplexLpSolver::OptimiseCore(mpq_class& precision) {
  const SoplexStatus status = spx_.optimize();
  Rational max_violation, sum_violation;

  // The status must be OPTIMAL, UNBOUNDED, or INFEASIBLE. Anything else is an error
  if (status != SoplexStatus::OPTIMAL && status != SoplexStatus::UNBOUNDED && status != SoplexStatus::INFEASIBLE) {
    DLINEAR_ERROR_FMT("SoplexLpSolver::Optimise: Unexpected SoPlex return -> {}", status);
    return LpResult::ERROR;
  } else if (spx_.getRowViolationRational(max_violation, sum_violation)) {
    precision = gmp::ToMpqClass(max_violation.backend().data());
    DLINEAR_DEBUG_FMT("SoplexLpSolver::Optimise: SoPlex returned {}, precision = {}", status, precision);
  } else {
    DLINEAR_DEBUG_FMT("SoplexLpSolver::Optimise: SoPlex has returned {}", status);
  }

  switch (status) {
    case SoplexStatus::OPTIMAL:
      UpdateFeasible();
      return max_violation.is_zero() ? LpResult::OPTIMAL : LpResult::DELTA_OPTIMAL;
    case SoplexStatus::UNBOUNDED:
      UpdateFeasible();
      return LpResult::UNBOUNDED;
    case SoplexStatus::INFEASIBLE:
      UpdateInfeasible();
      return LpResult::INFEASIBLE;
    default:
      DLINEAR_UNREACHABLE();
  }
}

void SoplexLpSolver::UpdateFeasible() {
  // Reset the infeasible information
  infeasible_bounds_ = std::nullopt;
  infeasible_rows_ = std::nullopt;

  // Set the feasible information
  const int colcount = num_columns();

  objective_value_ = gmp::ToMpqClass(spx_.objValueRational().backend().data());
  solution_ = std::make_optional<std::vector<mpq_class>>();
  solution_->reserve(colcount);
  soplex::VectorRational solution;
  solution.reDim(colcount);
  [[maybe_unused]] const bool has_sol = spx_.getPrimalRational(solution);
  DLINEAR_ASSERT(has_sol, "has_sol must be true");
  DLINEAR_ASSERT(solution.dim() >= colcount, "x.dim() must be >= colcount");
  for (int i = 0; i < solution.dim(); i++) solution_->emplace_back(gmp::ToMpqClass(solution[i].backend().data()));
}
void SoplexLpSolver::UpdateInfeasible() {
  // Reset the feasible information
  objective_value_ = std::nullopt;
  solution_ = std::nullopt;

  // Set the infeasible information
  infeasible_bounds_ = std::make_optional<std::vector<int>>();
  infeasible_rows_ = std::make_optional<std::vector<int>>();

  // Get the infeasible rows
  const int rowcount = num_rows();
  const int colcount = num_columns();

  infeasible_rows_->reserve(rowcount);
  infeasible_bounds_->reserve(colcount);

  soplex::VectorRational farkas_ray{rowcount};
  DLINEAR_ASSERT(farkas_ray.dim() == num_rows(), "farkas_ray must have the same dimension as the rows");
  // Get the Farkas ray to identify which rows are responsible for the conflict
  [[maybe_unused]] bool res = spx_.getDualFarkasRational(farkas_ray);
  DLINEAR_ASSERT(res, "getDualFarkasRational() must return true");

  // Add the non-zero rows to the infeasible core
  for (int i = 0; i < rowcount; i++) {
    if (farkas_ray[i].is_zero()) continue;
    DLINEAR_TRACE_FMT("SoplexLpSolver::UpdateInfeasible: ray[{}] = {}", i, farkas_ray[i]);
    infeasible_rows_->emplace_back(i);
  }
  //  Multiply the Farkas ray by the row coefficients to get the column violations: ray * A
  //  If the result is non-zero, the sign indicates the bound that caused the violation.
  Rational col_violation{0};
  for (int i = 0; i < colcount; i++) {
    col_violation = 0;
    for (int j = 0; j < rowcount; j++) {
      col_violation += farkas_ray[j] * spx_.rowVectorRational(j)[i];
    }
    if (col_violation.is_zero()) continue;
    DLINEAR_TRACE_FMT("SoplexLpSolver::UpdateInfeasible: {}[{}] = {}", col_to_var_.at(i), i, col_violation);
    infeasible_bounds_->emplace_back(col_violation > 0 ? i : -i);
  }
}

soplex::DSVectorRational SoplexLpSolver::ParseRowCoeff(const Formula& formula) {
  DLINEAR_ASSERT_FMT(formula.IsFlattened(), "The formula {} must be flattened", formula);

  const Expression& lhs = get_lhs_expression(formula);
  const Expression& rhs = get_rhs_expression(formula);
  DLINEAR_ASSERT(is_variable(lhs) || is_multiplication(lhs) || is_addition(lhs), "Unsupported expression");
  DLINEAR_ASSERT(is_constant(rhs), "Unsupported expression");

  soplex::DSVectorRational coeffs;
  rhs_.emplace_back(get_constant_value(rhs));

  if (is_variable(lhs)) {
    SetVarCoeff(coeffs, get_variable(lhs), 1);
  } else if (is_addition(lhs)) {
    DLINEAR_ASSERT(get_constant_in_addition(lhs) == 0, "The addition constant must be 0");
    const std::map<Expression, mpq_class>& map = get_expr_to_coeff_map_in_addition(lhs);
    coeffs.setMax(static_cast<int>(map.size()));
    for (const auto& [var, coeff] : map) {
      if (!is_variable(var)) DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", lhs);
      SetVarCoeff(coeffs, get_variable(var), coeff);
    }
  } else if (is_multiplication(lhs)) {
    DLINEAR_ASSERT(get_base_to_exponent_map_in_multiplication(lhs).size() == 1, "Only one variable is supported");
    DLINEAR_ASSERT(is_variable(get_base_to_exponent_map_in_multiplication(lhs).begin()->first),
                   "Base must be a variable");
    DLINEAR_ASSERT(is_constant(get_base_to_exponent_map_in_multiplication(lhs).begin()->second) &&
                       get_constant_value(get_base_to_exponent_map_in_multiplication(lhs).begin()->second) == 1,
                   "Only exp == 1 is supported");
    SetVarCoeff(coeffs, get_variable(get_base_to_exponent_map_in_multiplication(lhs).begin()->first),
                get_constant_in_multiplication(lhs));
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
  }
  if (rhs_.back() <= ninfinity_ || rhs_.back() >= infinity_) {
    DLINEAR_RUNTIME_ERROR_FMT("LP RHS value too large: {}", rhs_.back());
  }
  return coeffs;
}

void SoplexLpSolver::SetVarCoeff(soplex::DSVectorRational& coeffs, const Variable& var, const mpq_class& value) const {
  const auto it = var_to_col_.find(var);
  if (it == var_to_col_.end()) DLINEAR_RUNTIME_ERROR_FMT("Undefined variable in the SoPlex LP solver: {}", var);
  if (value <= ninfinity_ || value >= infinity_) {
    DLINEAR_RUNTIME_ERROR_FMT("LP coefficient too large for SoPlex: {}", value);
  }
  coeffs.add(it->second, gmp::ToMpq(value));
}

void SoplexLpSolver::Dump() { spx_.writeFileRational("~/dlinear.temp.dump.soplex.lp"); }

}  // namespace dlinear