/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "QsoptexTheorySolver.h"

#include <limits>
#include <map>
#include <utility>

#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

QsoptexTheorySolver::QsoptexTheorySolver(PredicateAbstractor &predicate_abstractor, const std::string &class_name)
    : TheorySolver(predicate_abstractor, class_name), qsx_{nullptr}, ray_{0}, x_{0} {
  qsopt_ex::QSXStart();
  qsx_ = mpq_QScreate_prob(nullptr, QS_MIN);
  DLINEAR_ASSERT(qsx_, "Failed to create QSopt_ex problem");
  if (config_.verbose_simplex() > 3) {
    DLINEAR_RUNTIME_ERROR("With --lp-solver qsoptex, maximum value for --verbose-simplex is 3");
  }
  mpq_QSset_param(qsx_, QS_PARAM_SIMPLEX_DISPLAY, config_.verbose_simplex());
  DLINEAR_DEBUG_FMT("QsoptexTheorySolver::QsoptexTheorySolver: precision = {}", config_.precision());
}

QsoptexTheorySolver::~QsoptexTheorySolver() {
  mpq_QSfree_prob(qsx_);
  qsopt_ex::QSXFinish();
}

void QsoptexTheorySolver::AddVariable(const Variable &var) {
  auto it = var_to_theory_col_.find(var.get_id());
  // The variable is already present
  if (it != var_to_theory_col_.end()) return;

  const int qsx_col = mpq_QSget_colcount(qsx_);
  [[maybe_unused]] int status = mpq_QSnew_col(qsx_, mpq_zeroLpNum, mpq_NINFTY, mpq_INFTY, var.get_name().c_str());
  DLINEAR_ASSERT(!status, "Invalid status");
  var_to_theory_col_.emplace(var.get_id(), qsx_col);
  theory_col_to_var_.emplace_back(var);
  fixed_preprocessor_.AddVariable(var);
  DLINEAR_DEBUG_FMT("QsoptexTheorySolver::AddVariable({} ↦ {})", var, qsx_col);
}

void QsoptexTheorySolver::AddLiterals() {
  qsx_rhs_.reserve(predicate_abstractor_.var_to_formula_map().size());
  qsx_sense_.reserve(predicate_abstractor_.var_to_formula_map().size());
  TheorySolver::AddLiterals();
}

void QsoptexTheorySolver::Consolidate(const Box &box) {
  if (is_consolidated_) return;

  // Clear variable bounds
  for (int theory_col = 0; theory_col < static_cast<int>(theory_col_to_var_.size()); theory_col++) {
    const Variable &var{theory_col_to_var_[theory_col]};
    DLINEAR_ASSERT(theory_col < mpq_QSget_colcount(qsx_), "theory_col must be in bounds");
    if (box.has_variable(var)) {
      DLINEAR_ASSERT(mpq_NINFTY <= box[var].lb(), "Lower bound too low");
      DLINEAR_ASSERT(box[var].lb() <= box[var].ub(), "Lower bound must be smaller than upper bound");
      DLINEAR_ASSERT(box[var].ub() <= mpq_INFTY, "Upper bound too high");
      fixed_preprocessor_.SetInfinityBounds(var, box[var].lb(), box[var].ub());
    }
  }
  preprocessor_.Clear(fixed_preprocessor_);

  TheorySolver::Consolidate(box);
}

void QsoptexTheorySolver::UpdateModelSolution() {
  DLINEAR_ASSERT(x_.size() >= static_cast<std::size_t>(mpq_QSget_rowcount(qsx_)), "x.dim() must be >= colcount");
  for (int theory_col = 0; theory_col < static_cast<int>(theory_col_to_var_.size()); theory_col++) {
    const Variable &var{theory_col_to_var_[theory_col]};
    DLINEAR_ASSERT(
        model_[var].lb() <= gmp::to_mpq_class(x_[theory_col]) && gmp::to_mpq_class(x_[theory_col]) <= model_[var].ub(),
        "val must be in bounds");
    model_[var] = x_[theory_col];
  }
}
void QsoptexTheorySolver::UpdateModelBounds() {
  DLINEAR_ASSERT(mpq_QSget_rowcount(qsx_) == 0, "There must be no rows in the LP solver");
  DLINEAR_ASSERT(std::all_of(theory_col_to_var_.cbegin(), theory_col_to_var_.cend(),
                             [this](const Variable &it) {
                               const int theory_col = &it - &theory_col_to_var_[0];
                               [[maybe_unused]] int res;
                               mpq_t temp;
                               mpq_init(temp);
                               res = mpq_QSget_bound(qsx_, theory_col, 'L', &temp);
                               DLINEAR_ASSERT(!res, "Invalid res");
                               mpq_class lb{temp};
                               res = mpq_QSget_bound(qsx_, theory_col, 'U', &temp);
                               DLINEAR_ASSERT(!res, "Invalid res");
                               mpq_class ub{temp};
                               mpq_clear(temp);
                               return lb <= ub;
                             }),
                 "All lower bounds must be <= upper bounds");

  // Update the box with the new bounds, since the theory solver won't be called, for there are no constraints.
  mpq_t temp;
  mpq_init(temp);
  for (int theory_col = 0; theory_col < static_cast<int>(theory_col_to_var_.size()); theory_col++) {
    const Variable &var{theory_col_to_var_[theory_col]};
    [[maybe_unused]] int res;
    res = mpq_QSget_bound(qsx_, theory_col, 'L', &temp);
    DLINEAR_ASSERT(!res, "Invalid res");
    mpq_class lb{temp};
    res = mpq_QSget_bound(qsx_, theory_col, 'U', &temp);
    DLINEAR_ASSERT(!res, "Invalid res");
    mpq_class ub{temp};
    mpq_class val;
    if (mpq_NINFTY < lb) {
      val = lb;
    } else if (ub < mpq_INFTY) {
      val = ub;
    } else {
      val = 0;
    }
    DLINEAR_ASSERT(model_[var].lb() <= val && val <= model_[var].ub(), "Val must be in bounds");
    model_[var] = val;
  }
  mpq_clear(temp);
}

void QsoptexTheorySolver::ClearLinearObjective() {
  const int qsx_colcount = mpq_QSget_colcount(qsx_);
  mpq_t c_value;
  mpq_init(c_value);
  mpq_set_d(c_value, 0);  // Initialized to zero
  // Set all objective coefficients to zero
  for (int i = 0; i < qsx_colcount; ++i) mpq_QSchange_objcoef(qsx_, i, c_value);
  mpq_clear(c_value);
}

void QsoptexTheorySolver::SetRowCoeff(const Formula &formula, const int qsx_row) {
  DLINEAR_ASSERT_FMT(formula.IsFlattened(), "The formula {} must be flattened", formula);

  const Expression &lhs = get_lhs_expression(formula);
  const Expression &rhs = get_rhs_expression(formula);
  DLINEAR_ASSERT(is_variable(lhs) || is_multiplication(lhs) || is_addition(lhs), "Unsupported expression");
  DLINEAR_ASSERT(is_constant(rhs), "Unsupported expression");

  qsx_rhs_.emplace_back(get_constant_value(rhs));

  if (is_variable(lhs)) {
    SetQsxVarCoeff(qsx_row, get_variable(lhs), 1);
  } else if (is_addition(lhs)) {
    DLINEAR_ASSERT(get_constant_in_addition(lhs) == 0, "The addition constant must be 0");
    const std::map<Expression, mpq_class> &map = get_expr_to_coeff_map_in_addition(lhs);
    for (const auto &[var, coeff] : map) {
      DLINEAR_ASSERT_FMT(is_variable(var), "Only variables are supported in the addition, got {}", var);
      SetQsxVarCoeff(qsx_row, get_variable(var), coeff);
    }
  } else if (is_multiplication(lhs)) {
    DLINEAR_ASSERT(get_base_to_exponent_map_in_multiplication(lhs).size() == 1, "Only one variable is supported");
    DLINEAR_ASSERT(is_variable(get_base_to_exponent_map_in_multiplication(lhs).begin()->first),
                   "Base must be a variable");
    DLINEAR_ASSERT(is_constant(get_base_to_exponent_map_in_multiplication(lhs).begin()->second) &&
                       get_constant_value(get_base_to_exponent_map_in_multiplication(lhs).begin()->second) == 1,
                   "Only exp == 1 is supported");
    SetQsxVarCoeff(qsx_row, get_variable(get_base_to_exponent_map_in_multiplication(lhs).begin()->first),
                   get_constant_in_multiplication(lhs));
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
  }
  if (qsx_rhs_.back() <= mpq_NINFTY || qsx_rhs_.back() >= mpq_INFTY) {
    DLINEAR_RUNTIME_ERROR_FMT("LP RHS value too large: {}", qsx_rhs_.back());
  }
}

void QsoptexTheorySolver::SetLinearObjective(const Expression &expr) {
  ClearLinearObjective();
  if (is_constant(expr)) {
    if (0 != get_constant_value(expr)) {
      DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported in objective", expr);
    }
  } else if (is_variable(expr)) {
    SetQsxVarObjCoeff(get_variable(expr), 1);
  } else if (is_addition(expr)) {
    const std::map<Expression, mpq_class> &map = get_expr_to_coeff_map_in_addition(expr);
    if (0 != get_constant_in_addition(expr)) {
      DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported in objective", expr);
    }
    for (const auto &[var, coeff] : map) {
      if (!is_variable(var)) {
        DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported in objective", expr);
      }
      SetQsxVarObjCoeff(get_variable(var), coeff);
    }
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported in objective", expr);
  }
}

void QsoptexTheorySolver::EnableQsxVarBound() {
  for (const auto &[var, bounds] : preprocessor_.theory_bounds()) {
    const int theory_col = var_to_theory_col_.at(var.get_id());
    mpq_QSchange_bound(qsx_, theory_col, 'L', bounds.active_lower_bound().get_mpq_t());
    mpq_QSchange_bound(qsx_, theory_col, 'U', bounds.active_upper_bound().get_mpq_t());
    DLINEAR_TRACE_FMT("EnableQsxVarBound: {} = [{}, {}]", var, bounds.active_lower_bound(),
                      bounds.active_upper_bound());
  }
}

void QsoptexTheorySolver::SetQsxVarCoeff(int qsx_row, const Variable &var, const mpq_class &value) {
  const auto it = var_to_theory_col_.find(var.get_id());
  // Variable is not present in the LP solver
  if (it == var_to_theory_col_.end()) DLINEAR_RUNTIME_ERROR("Variable undefined: {}");
  // Variable has the coefficients too large
  if (value <= mpq_NINFTY || value >= mpq_INFTY) DLINEAR_RUNTIME_ERROR_FMT("LP coefficient too large: {}", value);

  mpq_t c_value;
  mpq_init(c_value);
  mpq_set(c_value, value.get_mpq_t());
  mpq_QSchange_coef(qsx_, qsx_row, it->second, c_value);
  mpq_clear(c_value);
}

void QsoptexTheorySolver::SetQsxVarObjCoeff(const Variable &var, const mpq_class &value) {
  const auto it = var_to_theory_col_.find(var.get_id());
  // Variable is not present in the LP solver
  if (it == var_to_theory_col_.end()) DLINEAR_RUNTIME_ERROR_FMT("Variable undefined: {}", var);

  if (value <= mpq_NINFTY || value >= mpq_INFTY) DLINEAR_RUNTIME_ERROR_FMT("LP coefficient too large: {}", value);

  mpq_t c_value;
  mpq_init(c_value);
  mpq_set(c_value, value.get_mpq_t());
  mpq_QSchange_objcoef(qsx_, it->second, c_value);
  mpq_clear(c_value);
}

extern "C" void QsoptexCheckSatPartialSolution(mpq_QSdata const * /*prob*/, mpq_t *const /*x*/, const mpq_t infeas,
                                               const mpq_t /*delta*/, void *data) {
  DLINEAR_DEBUG_FMT("QsoptexTheorySolver::QsoptexCheckSatPartialSolution called with infeasibility {}",
                    mpq_class(infeas));
  auto *theory_solver = static_cast<QsoptexTheorySolver *>(data);
  // mpq_get_d() rounds towards 0.  This code guarantees infeas_gt > infeas.
  double infeas_gt = nextafter(mpq_get_d(infeas), std::numeric_limits<double>::infinity());
  std::cout << "PARTIAL: delta-sat with delta = " << infeas_gt << " ( > " << mpq_class{infeas} << ")";
  if (theory_solver->config().with_timings()) {
    std::cout << " after " << theory_solver->stats().timer().seconds() << " seconds";
  }
  std::cout << std::endl;
}

void QsoptexTheorySolver::UpdateExplanation(LiteralSet &explanation) {
  // TODO: the ray is not minimal in the slightest. It should be possible to improve it
  explanation.clear();
  // For each row in the ray
  for (int i = 0; i < static_cast<int>(ray_.size()); ++i) {
    if (mpq_sgn(ray_[i]) == 0) continue;  // The row did not participate in the conflict, ignore it
    if (DLINEAR_TRACE_ENABLED) {
      mpq_t temp;
      mpq_init(temp);
      mpq_QSget_bound(qsx_, i, 'L', &temp);
      mpq_class l{temp};
      mpq_QSget_bound(qsx_, i, 'U', &temp);
      mpq_class u{temp};
      mpq_clear(temp);
      DLINEAR_TRACE_FMT("QsoptexTheorySolver::UpdateExplanation: ray[{}] = {} <= {} <= {}", i, l, mpq_class{ray_[i]},
                        u);
    }
    const Literal &lit = theory_row_to_lit_[i];
    // Insert the conflicting row literal to the explanation. Use the latest truth value from the SAT solver
    explanation.insert(lit);
  }
  mpq_class col_violation{0};
  for (int i = 0; i < static_cast<int>(theory_col_to_var_.size()); i++) {
    col_violation = 0;
    for (int j = 0; j < mpq_QSget_rowcount(qsx_); j++) {
      if (mpq_sgn(ray_[j]) == 0) continue;
      mpq_t temp;
      mpq_init(temp);
      mpq_QSget_coef(qsx_, j, i, &temp);
      mpq_mul(temp, temp, ray_[j]);
      mpq_add(col_violation.get_mpq_t(), col_violation.get_mpq_t(), temp);
      mpq_clear(temp);
    }
    if (col_violation == 0) continue;
    DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::UpdateExplanationInfeasible: {}[{}] = {}", theory_col_to_var_[i], i,
                      col_violation);
    const BoundVector &bounds = preprocessor_.theory_bounds().at(theory_col_to_var_[i]);
    bounds.GetActiveBounds(col_violation < 0 ? bounds.active_lower_bound() : bounds.active_upper_bound())
        .explanation(explanation);
  }
}
void QsoptexTheorySolver::DisableQsxRows() {
  const int rowcount = mpq_QSget_rowcount(qsx_);
  for (int theory_row = 0; theory_row < rowcount; theory_row++) {
    if (!theory_rows_state_.at(theory_row)) {
      mpq_QSchange_sense(qsx_, theory_row, 'G');
      mpq_QSchange_rhscoef(qsx_, theory_row, mpq_NINFTY);
    }
  }
}
void QsoptexTheorySolver::EnableQsxRow(const int qsx_row) {
  const auto &[var, truth] = theory_row_to_lit_[qsx_row];
  EnableQsxRow(qsx_row, truth);
}

}  // namespace dlinear
