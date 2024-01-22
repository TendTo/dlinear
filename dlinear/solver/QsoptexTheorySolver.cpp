//
// Created by c3054737 on 15/01/24.
//

#include "QsoptexTheorySolver.h"

#include <limits>
#include <map>

#include "dlinear/util/Infinity.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

QsoptexTheorySolver::QsoptexTheorySolver(PredicateAbstractor &predicate_abstractor, const Config &config)
    : TheorySolver(predicate_abstractor, config),
      continuous_output_{config.continuous_output()},
      with_timings_{config.with_timings()},
      qsx_{mpq_QScreate_prob(nullptr, QS_MIN)} {
  DLINEAR_ASSERT(qsx_, "Failed to create QSopt_ex problem");
  if (config.verbose_simplex() > 3) {
    DLINEAR_RUNTIME_ERROR("With --lp-solver qsoptex, maximum value for --verbose-simplex is 3");
  }
  mpq_QSset_param(qsx_, QS_PARAM_SIMPLEX_DISPLAY, config.verbose_simplex());
  DLINEAR_DEBUG_FMT("QsoptexTheorySolver::QsoptexTheorySolver: precision = {}", config.precision());
}

QsoptexTheorySolver::~QsoptexTheorySolver() { mpq_QSfree_prob(qsx_); }

void QsoptexTheorySolver::AddVariable(const Variable &var) {
  auto it = var_to_theory_col_.find(var.get_id());
  // Found.
  if (it != var_to_theory_col_.end()) return;

  const int qsx_col = mpq_QSget_colcount(qsx_);
  [[maybe_unused]] int status = mpq_QSnew_col(qsx_, mpq_zeroLpNum, mpq_NINFTY, mpq_INFTY, var.get_name().c_str());
  DLINEAR_ASSERT(!status, "Invalid status");
  var_to_theory_col_.emplace(var.get_id(), qsx_col);
  theory_col_to_var_[qsx_col] = var;
  theory_bound_to_explanation_.emplace_back();
  DLINEAR_DEBUG_FMT("QsoptexTheorySolver::AddVariable({} ↦ {})", var, qsx_col);
}

void QsoptexTheorySolver::UpdateModelBounds() {
  DLINEAR_ASSERT(mpq_QSget_rowcount(qsx_) == 0, "There must be no rows in the LP solver");
  DLINEAR_ASSERT(std::all_of(theory_col_to_var_.cbegin(), theory_col_to_var_.cend(),
                             [this](const std::pair<int, Variable> &it) {
                               const auto &[theory_col, var] = it;
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
  for (const auto &[theory_col, var] : theory_col_to_var_) {
    [[maybe_unused]] int res;
    res = mpq_QSget_bound(qsx_, theory_col, 'L', &temp);
    DLINEAR_ASSERT(!res, "Invalid res");
    mpq_class lb{temp};
    res = mpq_QSget_bound(qsx_, theory_col, 'U', &temp);
    DLINEAR_ASSERT(!res, "Invalid res");
    mpq_class ub{temp};
    mpq_class val;
    if (Infinity::Ninfty() < lb) {
      val = lb;
    } else if (ub < Infinity::Infty()) {
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
  // Clear all the sets in the bounds to explanation map
  for (auto &explanation : theory_bound_to_explanation_) explanation.clear();
  // Clear constraint bounds
  const int qsx_rows{mpq_QSget_rowcount(qsx_)};
  DLINEAR_ASSERT(static_cast<size_t>(qsx_rows) == theory_row_to_lit_.size(), "Row count mismatch");
  for (int i = 0; i < qsx_rows; i++) {
    mpq_QSchange_sense(qsx_, i, 'G');
    mpq_QSchange_rhscoef(qsx_, i, mpq_NINFTY);
  }
  // Clear variable bounds
  [[maybe_unused]] const int qsx_cols{mpq_QSget_colcount(qsx_)};
  DLINEAR_ASSERT(static_cast<size_t>(qsx_cols) == theory_col_to_var_.size(), "Column count mismatch");
  for (const auto &[col_idx, var] : theory_col_to_var_) {
    if (box.has_variable(var)) {
      DLINEAR_ASSERT(Infinity::Ninfty() <= box[var].lb(), "Lower bound too low");
      DLINEAR_ASSERT(box[var].lb() <= box[var].ub(), "Lower bound must be smaller than upper bound");
      DLINEAR_ASSERT(box[var].ub() <= Infinity::Infty(), "Upper bound too high");
      mpq_QSchange_bound(qsx_, col_idx, 'L', box[var].lb().get_mpq_t());
      mpq_QSchange_bound(qsx_, col_idx, 'U', box[var].ub().get_mpq_t());
    } else {
      mpq_QSchange_bound(qsx_, col_idx, 'L', mpq_NINFTY);
      mpq_QSchange_bound(qsx_, col_idx, 'U', mpq_INFTY);
    }
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
  } else if (is_multiplication(expr)) {
    std::map<Expression, Expression> map = get_base_to_exponent_map_in_multiplication(expr);
    if (map.size() != 1 || !is_variable(map.begin()->first) || !is_constant(map.begin()->second) ||
        get_constant_value(map.begin()->second) != 1) {
      DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported in objective", expr);
    }
    SetQSXVarObjCoef(get_variable(map.begin()->first), get_constant_in_multiplication(expr));
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

void QsoptexTheorySolver::SetQSXVarCoef(int qsx_row, const Variable &var, const mpq_class &value) {
  const auto it = var_to_theory_col_.find(var.get_id());
  // Variable is not present in the LP solver
  if (it == var_to_theory_col_.end()) DLINEAR_RUNTIME_ERROR("Variable undefined: {}");
  // Variable has the coefficients too large
  if (value <= Infinity::Ninfty() || value >= Infinity::Infty()) {
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

  if (value <= Infinity::Ninfty() || value >= Infinity::Infty()) {
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
  if (value <= Infinity::Ninfty() || value >= Infinity::Infty()) {
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
  mpq_QSget_bound(qsx_, qsx_col, toChar(~type), &c_value);
  mpq_class opposite_bound{c_value};
  if ((type == LpColBound::L && opposite_bound < value) || (type == LpColBound::U && opposite_bound > value)) {
    DLINEAR_DEBUG_FMT("SoplexSatSolver::SetSPXVarBound: variable {} has invalid bounds [{}, {}]", var,
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
    fmt::print(" after {} seconds", main_timer.seconds());
  }
  fmt::print("\n");
}

void QsoptexTheorySolver::UpdateExplanation([[maybe_unused]] LiteralSet &explanation) {
  DLINEAR_RUNTIME_ERROR("Use UpdateExplanation(const qsopt_ex::MpqArray &ray, LiteralSet &explanation) instead");
}

void QsoptexTheorySolver::UpdateExplanation(const qsopt_ex::MpqArray &ray, LiteralSet &explanation) const {
  // TODO: the ray is not minimal in the slightest. It should be possible to improve it
  explanation.clear();
  // For each row in the ray
  for (int i = 0; i < static_cast<int>(ray.size()); ++i) {
    if (mpq_sgn(ray[i]) == 0) continue;  // The row did not participate in the conflict, ignore it
    if (DLINEAR_TRACE_ENABLED) {
      mpq_t temp;
      mpq_init(temp);
      mpq_QSget_bound(qsx_, i, 'L', &temp);
      mpq_class l{temp};
      mpq_QSget_bound(qsx_, i, 'U', &temp);
      mpq_class u{temp};
      mpq_clear(temp);
      DLINEAR_TRACE_FMT("QsoptexTheorySolver::UpdateExplanation: ray[{}] = {} <= {} <= {}", i, l, mpq_class{ray[i]}, u);
    }
    const Literal &lit = theory_row_to_lit_[i];
    // Insert the conflicting row literal to the explanation. Use the latest truth value from the SAT solver
    explanation.insert({lit.first, theory_row_to_truth_[i]});
    // For each free variable in the literal, add their bounds to the explanation
    for (const auto &col_var : predicate_abstractor_[lit.first].GetFreeVariables()) {
      const int theory_col = var_to_theory_col_.at(col_var.get_id());
      const LiteralSet &theory_bound_to_explanation = theory_bound_to_explanation_.at(theory_col);
      explanation.insert(theory_bound_to_explanation.cbegin(), theory_bound_to_explanation.cend());
    }
  }
}

}  // namespace dlinear
