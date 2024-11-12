/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "QsoptexLpSolver.h"

#include "dlinear/util/error.h"
#include "dlinear/util/logging.h"

namespace dlinear {

extern "C" void QsoptexCheckSatPartialSolution(mpq_QSdata const* /*prob*/, mpq_t* const /*x*/, const mpq_t infeas,
                                               const mpq_t /*delta*/, void* data) {
  DLINEAR_DEBUG_FMT("QsoptexTheorySolver::QsoptexCheckSatPartialSolution called with infeasibility {}",
                    mpq_class(infeas));
  auto* lp_solver = static_cast<QsoptexLpSolver*>(data);
  // mpq_get_d() rounds towards 0.  This code guarantees infeas_gt > infeas.
  double infeas_gt = nextafter(mpq_get_d(infeas), std::numeric_limits<double>::infinity());
  std::cout << "PARTIAL: delta-sat with delta = " << infeas_gt << " ( > " << mpq_class{infeas} << ")";
  if (lp_solver->config().with_timings()) {
    std::cout << " after " << lp_solver->stats().timer().seconds() << " seconds";
  }
  std::cout << std::endl;
}

QsoptexLpSolver::QsoptexLpSolver(const Config& config, const std::string& class_name)
    : LpSolver{config, 0, 0, class_name}, qsx_{nullptr}, ray_{0}, x_{0} {
  qsopt_ex::QSXStart();
  ninfinity_ = mpq_class{mpq_NINFTY};
  infinity_ = mpq_class{mpq_INFTY};

  qsx_ = mpq_QScreate_prob(nullptr, QS_MAX);
  DLINEAR_ASSERT(qsx_ != nullptr, "Failed to create QSopt_ex problem");
  if (config_.verbose_simplex() > 3) {
    DLINEAR_RUNTIME_ERROR("With --lp-solver qsoptex, maximum value for --verbose-simplex is 3");
  }
  [[maybe_unused]] const int status = mpq_QSset_param(qsx_, QS_PARAM_SIMPLEX_DISPLAY, config_.verbose_simplex());
  DLINEAR_ASSERT(!status, "Invalid status");
  DLINEAR_DEBUG_FMT("QsoptexTheorySolver::QsoptexTheorySolver: precision = {}", config_.precision());
}

QsoptexLpSolver::~QsoptexLpSolver() {
  mpq_QSfree_prob(qsx_);
  qsopt_ex::QSXFinish();
}

int QsoptexLpSolver::num_columns() const { return mpq_QSget_colcount(qsx_); }
int QsoptexLpSolver::num_rows() const { return mpq_QSget_rowcount(qsx_); }

void QsoptexLpSolver::AddColumn() {
  DLINEAR_ASSERT(!consolidated_, "Cannot add columns after consolidation.");
  // Add the column to the LP
  [[maybe_unused]] const int status = mpq_QSnew_col(qsx_, mpq_zeroLpNum, mpq_NINFTY, mpq_INFTY, nullptr);
  DLINEAR_ASSERT(!status, "Invalid status");
}
void QsoptexLpSolver::AddColumn(const mpq_class& lb, const mpq_class& ub) {
  DLINEAR_ASSERT(!consolidated_, "Cannot add columns after consolidation.");
  // Add the column to the LP
  [[maybe_unused]] const int status = mpq_QSnew_col(qsx_, mpq_zeroLpNum, lb.get_mpq_t(), ub.get_mpq_t(), nullptr);
  DLINEAR_ASSERT(!status, "Invalid status");
}
void QsoptexLpSolver::AddColumn(const mpq_class& obj, const mpq_class& lb, const mpq_class& ub) {
  DLINEAR_ASSERT(!consolidated_, "Cannot add columns after consolidation.");
  // Add the column to the LP
  [[maybe_unused]] const int status = mpq_QSnew_col(qsx_, obj.get_mpq_t(), lb.get_mpq_t(), ub.get_mpq_t(), nullptr);
  DLINEAR_ASSERT(!status, "Invalid status");
}
void QsoptexLpSolver::AddRow(const Formula& formula, LpRowSense sense) {
  [[maybe_unused]] const int status = mpq_QSnew_row(qsx_, mpq_NINFTY, 'G', nullptr);
  DLINEAR_ASSERT(!status, "Invalid status");
  senses_.emplace_back(sense);
  SetRowCoeff(num_rows() - 1, formula);
}
void QsoptexLpSolver::SetObjective(int column, const mpq_class& value) {
  DLINEAR_ASSERT_FMT(column < num_columns(), "Column index out of bounds: {} >= {}", column, num_columns());
  [[maybe_unused]] const int status = mpq_QSchange_objcoef(qsx_, column, mpq_class{value}.get_mpq_t());
  DLINEAR_ASSERT(!status, "Invalid status");
}
void QsoptexLpSolver::EnableRow(const int row, const LpRowSense sense, const mpq_class& rhs) {
  DLINEAR_ASSERT_FMT(row < num_rows(), "Row index out of bounds: {} >= {}", row, num_rows());
  DLINEAR_ASSERT_FMT(ninfinity_ <= rhs && rhs <= infinity_, "LP RHS value too large: {} <= {} <= {}", ninfinity_, rhs,
                     infinity_);
  DLINEAR_ASSERT_FMT(
      sense == LpRowSense::EQ || sense == LpRowSense::LE || sense == LpRowSense::GE || sense == LpRowSense::NQ,
      "Unsupported sense {}", sense);
  if (sense == LpRowSense::NQ) {
    DisableRow(row);
    return;
  }

  const char qsx_sense = toChar(sense);
  mpq_QSchange_sense(qsx_, row, qsx_sense);
  [[maybe_unused]] const int status = mpq_QSchange_rhscoef(qsx_, row, mpq_class{rhs}.get_mpq_t());
  DLINEAR_ASSERT(!status, "Invalid status");
}
void QsoptexLpSolver::EnableBound(const int column, const LpColBound bound, const mpq_class& value) {
  [[maybe_unused]] int status = 0;
  switch (bound) {
    case LpColBound::B:
      status = mpq_QSchange_bound(qsx_, column, 'L', value.get_mpq_t());
      status = mpq_QSchange_bound(qsx_, column, 'U', value.get_mpq_t());
      break;
    case LpColBound::L:
      status = mpq_QSchange_bound(qsx_, column, 'L', value.get_mpq_t());
      status = mpq_QSchange_bound(qsx_, column, 'U', infinity_.get_mpq_t());
      break;
    case LpColBound::U:
      status = mpq_QSchange_bound(qsx_, column, 'L', ninfinity_.get_mpq_t());
      status = mpq_QSchange_bound(qsx_, column, 'U', value.get_mpq_t());
      break;
    case LpColBound::F:
    case LpColBound::D:
      DisableBound(column);
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
  DLINEAR_ASSERT(!status, "Invalid status");
}
void QsoptexLpSolver::EnableBound(const int column, const mpq_class& lb, const mpq_class& ub) {
  [[maybe_unused]] int status = mpq_QSchange_bound(qsx_, column, 'L', lb.get_mpq_t());
  DLINEAR_ASSERT(!status, "Invalid status");
  status = mpq_QSchange_bound(qsx_, column, 'U', ub.get_mpq_t());
  DLINEAR_ASSERT(!status, "Invalid status");
  DLINEAR_TRACE_FMT("EnableQsxVarBound: {} = [{}, {}]", col_to_var_.at(column), lb, ub);
}
void QsoptexLpSolver::DisableBound(const int column) { EnableBound(column, ninfinity_, infinity_); }
void QsoptexLpSolver::DisableRow(const int row) {
  [[maybe_unused]] int status = mpq_QSchange_sense(qsx_, row, 'G');
  DLINEAR_ASSERT(!status, "Invalid status");
  status = mpq_QSchange_rhscoef(qsx_, row, mpq_NINFTY);
  DLINEAR_ASSERT(!status, "Invalid status");
}

LpResult QsoptexLpSolver::OptimiseCore(mpq_class& precision, const bool store_solution) {
  const std::size_t rowcount = num_rows();
  const std::size_t colcount = num_columns();
  // x: must be allocated/deallocated using QSopt_ex.
  // Should have room for the (rowcount) "logical" variables, which come after the (colcount) "structural" variables.
  x_.Resize(colcount + rowcount);
  ray_.Resize(rowcount);

  int lp_status = -1;
  int status = -1;

  if (1 == config_.simplex_sat_phase()) {
    status = QSdelta_solver(qsx_, precision.get_mpq_t(), static_cast<mpq_t*>(x_), static_cast<mpq_t*>(ray_), nullptr,
                            PRIMAL_SIMPLEX, &lp_status,
                            config_.continuous_output() ? QsoptexCheckSatPartialSolution : nullptr, this);
  } else {
    status = QSexact_delta_solver(qsx_, static_cast<mpq_t*>(x_), static_cast<mpq_t*>(ray_), nullptr, PRIMAL_SIMPLEX,
                                  &lp_status, precision.get_mpq_t(),
                                  config_.continuous_output() ? QsoptexCheckSatPartialSolution : nullptr, this);
  }

  if (status) {
    DLINEAR_RUNTIME_ERROR_FMT("QSopt_ex returned {}", status);
    return LpResult::ERROR;
  }

  DLINEAR_DEBUG_FMT("DeltaQsoptexTheorySolver::CheckSat: QSopt_ex has returned with precision = {}", precision);

  switch (lp_status) {
    case QS_LP_FEASIBLE:
    case QS_LP_DELTA_FEASIBLE:
      if (store_solution) UpdateFeasible();
      return lp_status == QS_LP_FEASIBLE ? LpResult::OPTIMAL : LpResult::DELTA_OPTIMAL;
    case QS_LP_UNBOUNDED:
      if (store_solution) UpdateFeasible();
      return LpResult::UNBOUNDED;
    case QS_LP_INFEASIBLE:
      UpdateInfeasible();
      return LpResult::INFEASIBLE;
    case QS_LP_UNSOLVED:
      DLINEAR_WARN("DeltaQsoptexTheorySolver::CheckSat: QSopt_ex failed to return a result");
      return LpResult::ERROR;
    default:
      DLINEAR_UNREACHABLE();
  }
}

void QsoptexLpSolver::UpdateFeasible() {
  DLINEAR_ASSERT(solution_.empty(), "Solution must be empty");
  DLINEAR_ASSERT(dual_solution_.empty(), "Dual solution must be empty");
  // Set the feasible information
  const int colcount = num_columns();
  const int rowcount = num_rows();

  for (int i = 0; i < colcount; i++) solution_.emplace_back(x_[i]);

  for (int i = 0; i < rowcount; i++) dual_solution_.emplace_back(ray_[i]);

  DLINEAR_DEV_FMT("solution {}", solution_);
  DLINEAR_DEV_FMT("dual {}", dual_solution_);
}
void QsoptexLpSolver::UpdateInfeasible() {
  DLINEAR_ASSERT(infeasible_rows_.empty(), "Infeasible rows must be empty");
  DLINEAR_ASSERT(infeasible_bounds_.empty(), "Infeasible bounds must be empty");
  // Set the infeasible information
  const int rowcount = num_rows();
  const int colcount = num_columns();

  // Add the non-zero rows to the infeasible core
  for (int i = 0; i < rowcount; i++) {
    if (mpq_sgn(ray_[i]) == 0) continue;
    DLINEAR_TRACE_FMT("QsoptexLpSolver::NotifyInfeasible: ray[{}] = {}", i, gmp::ToMpqClass(ray_[i]));
    infeasible_rows_.emplace_back(i);
  }
  //  Multiply the Farkas ray by the row coefficients to get the column violations: ray * A
  //  If the result is non-zero, the sign indicates the bound that caused the violation.
  mpq_class col_violation{0};
  mpq_t row_coeff;
  mpq_init(row_coeff);
  for (int i = 0; i < colcount; i++) {
    col_violation = 0;
    for (int j = 0; j < rowcount; j++) {
      mpq_QSget_coef(qsx_, j, i, &row_coeff);
      col_violation += gmp::ToMpqClass(ray_[j]) * gmp::ToMpqClass(row_coeff);
    }
    if (col_violation == 0) continue;
    DLINEAR_TRACE_FMT("QsoptexLpSolver::NotifyInfeasible: {}[{}] = {}", col_to_var_.at(i), i, col_violation);
    infeasible_bounds_.emplace_back(i, col_violation > 0);
  }
  mpq_clear(row_coeff);
}

void QsoptexLpSolver::SetRowCoeff(const int row, const Formula& formula) {
  DLINEAR_ASSERT_FMT(formula.IsFlattened(), "The formula {} must be flattened", formula);

  const Expression& lhs = get_lhs_expression(formula);
  const Expression& rhs = get_rhs_expression(formula);
  DLINEAR_ASSERT(is_variable(lhs) || is_multiplication(lhs) || is_addition(lhs), "Unsupported expression");
  DLINEAR_ASSERT(is_constant(rhs), "Unsupported expression");

  rhs_.emplace_back(get_constant_value(rhs));

  if (is_variable(lhs)) {
    SetVarCoeff(row, get_variable(lhs), 1);
  } else if (is_addition(lhs)) {
    DLINEAR_ASSERT(get_constant_in_addition(lhs) == 0, "The addition constant must be 0");
    const std::map<Expression, mpq_class>& map = get_expr_to_coeff_map_in_addition(lhs);
    for (const auto& [var, coeff] : map) {
      DLINEAR_ASSERT_FMT(is_variable(var), "Only variables are supported in the addition, got {}", var);
      SetVarCoeff(row, get_variable(var), coeff);
    }
  } else if (is_multiplication(lhs)) {
    DLINEAR_ASSERT(get_base_to_exponent_map_in_multiplication(lhs).size() == 1, "Only one variable is supported");
    DLINEAR_ASSERT(is_variable(get_base_to_exponent_map_in_multiplication(lhs).begin()->first),
                   "Base must be a variable");
    DLINEAR_ASSERT(is_constant(get_base_to_exponent_map_in_multiplication(lhs).begin()->second) &&
                       get_constant_value(get_base_to_exponent_map_in_multiplication(lhs).begin()->second) == 1,
                   "Only exp == 1 is supported");
    SetVarCoeff(row, get_variable(get_base_to_exponent_map_in_multiplication(lhs).begin()->first),
                get_constant_in_multiplication(lhs));
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
  }
  if (rhs_.back() <= ninfinity_ || rhs_.back() >= infinity_) {
    DLINEAR_RUNTIME_ERROR_FMT("LP RHS value too large: {}", rhs_.back());
  }
}

void QsoptexLpSolver::SetVarCoeff(const int row, const Variable& var, const mpq_class& value) const {
  const int column = var_to_col_.at(var);
  // Variable has the coefficients too large
  if (value <= ninfinity_ || value >= infinity_) DLINEAR_RUNTIME_ERROR_FMT("LP coefficient too large: {}", value);

  mpq_t c_value;
  mpq_init(c_value);
  mpq_set(c_value, value.get_mpq_t());
  [[maybe_unused]] const int status = mpq_QSchange_coef(qsx_, row, column, c_value);
  DLINEAR_ASSERT(!status, "Invalid status");
  mpq_clear(c_value);
}

void QsoptexLpSolver::Dump() { mpq_QSdump_prob(qsx_); }
void QsoptexLpSolver::SetCoefficient(const int row, const int column, const mpq_class& value) {
  DLINEAR_ASSERT_FMT(row < num_rows(), "Row index out of bounds: {} >= {}", row, num_rows());
  DLINEAR_ASSERT_FMT(column < num_columns(), "Column index out of bounds: {} >= {}", column, num_columns());
  DLINEAR_ASSERT_FMT(value <= infinity_ && value >= ninfinity_, "LP coefficient too large: {}", value);

  [[maybe_unused]] const int status = mpq_QSchange_coef(qsx_, row, column, mpq_class{value}.get_mpq_t());
  DLINEAR_ASSERT(!status, "Invalid status");
}

}  // namespace dlinear