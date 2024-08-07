/**
 * @file QsoptexTheorySolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "QsoptexTheorySolver.h"

#include <limits>
#include <map>
#include <utility>

#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

const mpq_class QsoptexTheorySolver::infinity{mpq_INFTY};
const mpq_class QsoptexTheorySolver::ninfinity{mpq_NINFTY};

QsoptexTheorySolver::QsoptexTheorySolver(PredicateAbstractor &predicate_abstractor, const std::string &class_name)
    : TheorySolver(predicate_abstractor, class_name),
      continuous_output_{config_.continuous_output()},
      with_timings_{config_.with_timings()},
      qsx_{nullptr},
      ray_{1} {
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
  theory_bounds_.emplace_back(mpq_class{mpq_NINFTY}, mpq_class{mpq_INFTY});
  DLINEAR_DEBUG_FMT("QsoptexTheorySolver::AddVariable({} ↦ {})", var, qsx_col);
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
    if (QsoptexTheorySolver::ninfinity < lb) {
      val = lb;
    } else if (ub < QsoptexTheorySolver::infinity) {
      val = ub;
    } else {
      val = 0;
    }
    DLINEAR_ASSERT(model_[var].lb() <= val && val <= model_[var].ub(), "Val must be in bounds");
    model_[var] = val;
  }
  mpq_clear(temp);
}

void QsoptexTheorySolver::Reset(const Box &box) {
  DLINEAR_TRACE_FMT("QsoptexTheorySolver::Reset(): Box =\n{}", box);
  Consolidate();
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before resetting it");

  // Clear constraint bounds
  for (auto &bound : theory_bounds_) bound.Clear();
  const int qsx_rows{mpq_QSget_rowcount(qsx_)};
  DLINEAR_ASSERT(static_cast<size_t>(qsx_rows) == theory_row_to_lit_.size(), "Row count mismatch");
  for (int i = 0; i < qsx_rows; i++) {
    mpq_QSchange_sense(qsx_, i, 'G');
    mpq_QSchange_rhscoef(qsx_, i, mpq_NINFTY);
  }
  // Clear variable bounds
  [[maybe_unused]] const int qsx_cols{mpq_QSget_colcount(qsx_)};
  for (int theory_col = 0; theory_col < static_cast<int>(theory_col_to_var_.size()); theory_col++) {
    const Variable &var{theory_col_to_var_[theory_col]};
    DLINEAR_ASSERT(0 <= theory_col && theory_col < qsx_cols, "theory_col must be in bounds");
    if (box.has_variable(var)) {
      DLINEAR_ASSERT(QsoptexTheorySolver::ninfinity <= box[var].lb(), "Lower bound too low");
      DLINEAR_ASSERT(box[var].lb() <= box[var].ub(), "Lower bound must be smaller than upper bound");
      DLINEAR_ASSERT(box[var].ub() <= QsoptexTheorySolver::infinity, "Upper bound too high");
      theory_bounds_[theory_col].SetBounds(box[var].lb(), box[var].ub());
    }
    mpq_QSchange_bound(qsx_, theory_col, 'L', mpq_NINFTY);
    mpq_QSchange_bound(qsx_, theory_col, 'U', mpq_INFTY);
  }
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

void QsoptexTheorySolver::SetLinearObjective(const Expression &expr) {
  ClearLinearObjective();
  if (is_constant(expr)) {
    if (0 != get_constant_value(expr)) {
      DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported in objective", expr);
    }
  } else if (is_variable(expr)) {
    SetQSXVarObjCoef(get_variable(expr), 1);
  } else if (is_addition(expr)) {
    const std::map<Expression, mpq_class> &map = get_expr_to_coeff_map_in_addition(expr);
    if (0 != get_constant_in_addition(expr)) {
      DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported in objective", expr);
    }
    for (const auto &[var, coeff] : map) {
      if (!is_variable(var)) {
        DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported in objective", expr);
      }
      SetQSXVarObjCoef(get_variable(var), coeff);
    }
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported in objective", expr);
  }
}

void QsoptexTheorySolver::SetQPXVarBound() {
  for (int theory_col = 0; theory_col < static_cast<int>(theory_bounds_.size()); theory_col++) {
    mpq_QSchange_bound(qsx_, theory_col, 'L', theory_bounds_[theory_col].active_lower_bound().get_mpq_t());
    mpq_QSchange_bound(qsx_, theory_col, 'U', theory_bounds_[theory_col].active_upper_bound().get_mpq_t());
  }
}

void QsoptexTheorySolver::SetQSXVarCoef(int qsx_row, const Variable &var, const mpq_class &value) {
  const auto it = var_to_theory_col_.find(var.get_id());
  // Variable is not present in the LP solver
  if (it == var_to_theory_col_.end()) DLINEAR_RUNTIME_ERROR("Variable undefined: {}");
  // Variable has the coefficients too large
  if (value <= QsoptexTheorySolver::ninfinity || value >= QsoptexTheorySolver::infinity) {
    DLINEAR_RUNTIME_ERROR_FMT("LP coefficient too large: {}", value);
  }

  mpq_t c_value;
  mpq_init(c_value);
  mpq_set(c_value, value.get_mpq_t());
  mpq_QSchange_coef(qsx_, qsx_row, it->second, c_value);
  mpq_clear(c_value);
}

void QsoptexTheorySolver::SetQSXVarObjCoef(const Variable &var, const mpq_class &value) {
  const auto it = var_to_theory_col_.find(var.get_id());
  // Variable is not present in the LP solver
  if (it == var_to_theory_col_.end()) DLINEAR_RUNTIME_ERROR_FMT("Variable undefined: {}", var);

  if (value <= QsoptexTheorySolver::ninfinity || value >= QsoptexTheorySolver::infinity) {
    DLINEAR_RUNTIME_ERROR_FMT("LP coefficient too large: {}", value);
  }
  mpq_t c_value;
  mpq_init(c_value);
  mpq_set(c_value, value.get_mpq_t());
  mpq_QSchange_objcoef(qsx_, it->second, c_value);
  mpq_clear(c_value);
}

bool QsoptexTheorySolver::SetQSXVarBound(const Bound &bound, int qsx_col) {
  const auto &[var, type, value] = bound;
  DLINEAR_ASSERT_FMT(type == LpColBound::L || type == LpColBound::U || type == LpColBound::B || type == LpColBound::F,
                     "type must be 'L', 'U', 'B' or 'N', received {}", type);

  // Add both bounds
  if (type == LpColBound::B) {
    return SetQSXVarBound({var, LpColBound::L, value}, qsx_col) && SetQSXVarBound({var, LpColBound::U, value}, qsx_col);
  }

  DLINEAR_ASSERT(type == LpColBound::L || type == LpColBound::U, "Type must be '<=' or '>='");
  if (value <= QsoptexTheorySolver::ninfinity || value >= QsoptexTheorySolver::infinity) {
    DLINEAR_RUNTIME_ERROR_FMT("Simple bound too large: {}", value);
  }

  mpq_t c_value;
  mpq_init(c_value);

  mpq_QSget_bound(qsx_, qsx_col, toChar(type), &c_value);
  mpq_class existing{c_value};
  if ((type == LpColBound::L && value > existing) || (type == LpColBound::U && value < existing)) {
    mpq_set(c_value, value.get_mpq_t());
    mpq_QSchange_bound(qsx_, qsx_col, toChar(type), c_value);
  }

  // Make sure there are no inverted bounds
  mpq_QSget_bound(qsx_, qsx_col, toChar(-type), &c_value);
  mpq_class opposite_bound{c_value};
  if ((type == LpColBound::L && opposite_bound < value) || (type == LpColBound::U && opposite_bound > value)) {
    DLINEAR_DEBUG_FMT("SoplexSatSolver::EnableSPXVarBound: variable {} has invalid bounds [{}, {}]", var,
                      type == LpColBound::L ? value : opposite_bound, type == LpColBound::L ? opposite_bound : value);
    return false;
  }

  mpq_clear(c_value);
  return true;
}

extern "C" void QsoptexCheckSatPartialSolution(mpq_QSdata const * /*prob*/, mpq_t *const /*x*/, const mpq_t infeas,
                                               const mpq_t /*delta*/, void *data) {
  DLINEAR_DEBUG_FMT("QsoptexTheorySolver::QsoptexCheckSatPartialSolution called with infeasibility {}",
                    mpq_class(infeas));
  auto *theory_solver = static_cast<QsoptexTheorySolver *>(data);
  // mpq_get_d() rounds towards 0.  This code guarantees infeas_gt > infeas.
  double infeas_gt = nextafter(mpq_get_d(infeas), std::numeric_limits<double>::infinity());
  // fmt::print uses shortest round-trip format for doubles, by default
  fmt::print("PARTIAL: delta-sat with delta = {} ( > {})", infeas_gt, mpq_class(infeas));
  if (theory_solver->with_timings_) {
    fmt::print(" after {} seconds", theory_solver->stats_.timer().seconds());
  }
  fmt::print("\n");
}

void QsoptexTheorySolver::UpdateExplanation([[maybe_unused]] LiteralSet &explanation) {
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
    // For each free variable in the literal, add their bounds to the explanation
    for (const auto &col_var : predicate_abstractor_[lit.var].GetFreeVariables()) {
      const int theory_col = var_to_theory_col_.at(col_var.get_id());
      TheoryBoundsToExplanation(theory_col, explanation);
    }
  }
}

}  // namespace dlinear
