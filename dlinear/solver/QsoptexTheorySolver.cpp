//
// Created by c3054737 on 15/01/24.
//

#include "QsoptexTheorySolver.h"

#include "dlinear/util/Infinity.h"
#include "dlinear/util/Stats.h"
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

void QsoptexTheorySolver::AddLiteral(const Literal &lit) {
  const auto &[formulaVar, truth] = lit;
  const auto &var_to_formula_map = predicate_abstractor_.var_to_formula_map();
  const auto it = var_to_formula_map.find(formulaVar);
  // Boolean variable - no need to involve theory solver
  if (it == var_to_formula_map.end()) return;

  const auto it2 = lit_to_theory_row_.find({formulaVar.get_id(), truth});
  // Found.
  if (it2 != lit_to_theory_row_.end()) return;

  // Theory formula
  const Formula &formula = it->second;
  // Create the LP solver variables
  for (const Variable &var : formula.GetFreeVariables()) {
    AddVariable(var);
  }
  if (IsEqualToOrWhatever(formula, truth)) {
    if (IsSimpleBound(formula)) {
      return;  // Just create simple bound in LP
    }
    qsx_sense_.push_back('E');
  } else if (IsGreaterThanOrWhatever(formula, truth)) {
    if (IsSimpleBound(formula)) {
      return;
    }
    qsx_sense_.push_back('G');
  } else if (IsLessThanOrWhatever(formula, truth)) {
    if (IsSimpleBound(formula)) {
      return;
    }
    qsx_sense_.push_back('L');
  } else if (IsNotEqualToOrWhatever(formula, truth)) {
    // Nothing to do, because this constraint is always delta-sat for
    // delta > 0.
    return;
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
  }

  Expression expr;
  expr = (get_lhs_expression(formula) - get_rhs_expression(formula)).Expand();
  const int qsx_row{mpq_QSget_rowcount(qsx_)};
  mpq_QSnew_row(qsx_, mpq_NINFTY, 'G', nullptr);  // Inactive
  DLINEAR_ASSERT(static_cast<size_t>(qsx_row) == qsx_sense_.size() - 1, "Sense count mismatch");
  DLINEAR_ASSERT(static_cast<size_t>(qsx_row) == qsx_rhs_.size(), "RHS count mismatch");
  qsx_rhs_.emplace_back(0);
  if (is_constant(expr)) {
    qsx_rhs_.back() = -get_constant_value(expr);
  } else if (is_variable(expr)) {
    SetQSXVarCoef(qsx_row, get_variable(expr), 1);
  } else if (is_multiplication(expr)) {
    std::map<Expression, Expression> map = get_base_to_exponent_map_in_multiplication(expr);
    if (map.size() != 1 || !is_variable(map.begin()->first) || !is_constant(map.begin()->second) ||
        get_constant_value(map.begin()->second) != 1) {
      DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", expr);
    }
    SetQSXVarCoef(qsx_row, get_variable(map.begin()->first), get_constant_in_multiplication(expr));
  } else if (is_addition(expr)) {
    const std::map<Expression, mpq_class> &map = get_expr_to_coeff_map_in_addition(expr);
    for (const auto &pair : map) {
      if (!is_variable(pair.first)) {
        DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", expr);
      }
      SetQSXVarCoef(qsx_row, get_variable(pair.first), pair.second);
    }
    qsx_rhs_.back() = -get_constant_in_addition(expr);
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", expr);
  }
  if (qsx_rhs_.back() <= Infinity::Ninfty() || qsx_rhs_.back() >= Infinity::Infty()) {
    DLINEAR_RUNTIME_ERROR_FMT("LP RHS value too large: {}", qsx_rhs_.back());
  }
  // Update indexes
  lit_to_theory_row_.emplace(std::make_pair(formulaVar.get_id(), truth), std::make_pair(qsx_row, -1));
  DLINEAR_ASSERT(static_cast<size_t>(qsx_row) == theory_row_to_lit_.size(), "Row count mismatch");
  theory_row_to_lit_.emplace_back(formulaVar, truth);
  DLINEAR_DEBUG_FMT("QsoptexTheorySolver::AddLinearLiteral({}{} ↦ {})", truth ? "" : "¬", it->second, qsx_row);
}

void QsoptexTheorySolver::AddVariable(const Variable &var) {
  auto it = var_to_theory_col_.find(var.get_id());
  // Found.
  if (it != var_to_theory_col_.end()) return;

  const int qsx_col = mpq_QSget_colcount(qsx_);
  [[maybe_unused]] int status = mpq_QSnew_col(qsx_, mpq_zeroLpNum, mpq_NINFTY, mpq_INFTY, var.get_name().c_str());
  DLINEAR_ASSERT(!status, "Invalid status");
  var_to_theory_col_.emplace(var.get_id(), qsx_col);
  theory_col_to_var_[qsx_col] = var;
  DLINEAR_DEBUG_FMT("QsoptexTheorySolver::AddVariable({} ↦ {})", var, qsx_col);
}

void QsoptexTheorySolver::EnableLiteral(const Literal &lit) {
  const auto &[var, truth] = lit;
  const auto it_row = lit_to_theory_row_.find({var.get_id(), truth});
  if (it_row != lit_to_theory_row_.end()) {
    // A non-trivial linear literal from the input problem
    const auto &[qsx_row, qsx_row2] = it_row->second;
    mpq_QSchange_sense(qsx_, qsx_row, qsx_sense_[qsx_row]);
    mpq_QSchange_rhscoef(qsx_, qsx_row, qsx_rhs_[qsx_row].get_mpq_t());
    DLINEAR_TRACE_FMT("QsoptexTheorySolver::EnableLinearLiteral({})", qsx_row);
    return;
  }
  const auto &var_to_formula_map = predicate_abstractor_.var_to_formula_map();
  const auto it = var_to_formula_map.find(var);
  // Either a learned literal, or a not-equal literal from the input problem.
  if (it == var_to_formula_map.end() || !IsSimpleBound(it->second)) {
    DLINEAR_TRACE_FMT("QsoptexTheorySolver::EnableLinearLiteral: ignoring ({}, {})", var, truth);
    return;
  }

  // A simple bound - set it directly
  const Formula &formula{it->second};
  const Expression &lhs{get_lhs_expression(formula)};
  const Expression &rhs{get_rhs_expression(formula)};
  DLINEAR_TRACE_FMT("QsoptexTheorySolver::EnableLinearLiteral({}{})", truth ? "" : "¬", formula);
  if (IsEqualToOrWhatever(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) {
      SetQSXVarBound(get_variable(lhs), 'B', get_constant_value(rhs));
    } else if (is_constant(lhs) && is_variable(rhs)) {
      SetQSXVarBound(get_variable(rhs), 'B', get_constant_value(lhs));
    } else {
      DLINEAR_UNREACHABLE();
    }
  } else if (IsGreaterThanOrWhatever(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) {
      SetQSXVarBound(get_variable(lhs), 'L', get_constant_value(rhs));
    } else if (is_constant(lhs) && is_variable(rhs)) {
      SetQSXVarBound(get_variable(rhs), 'U', get_constant_value(lhs));
    } else {
      DLINEAR_UNREACHABLE();
    }
  } else if (IsLessThanOrWhatever(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) {
      SetQSXVarBound(get_variable(lhs), 'U', get_constant_value(rhs));
    } else if (is_constant(lhs) && is_variable(rhs)) {
      SetQSXVarBound(get_variable(rhs), 'L', get_constant_value(lhs));
    } else {
      DLINEAR_UNREACHABLE();
    }
  } else if (IsNotEqualToOrWhatever(formula, truth)) {
    // Nothing to do, because this constraint is always delta-sat for
    // delta > 0.
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
  }
}

SatResult QsoptexTheorySolver::CheckSat(const Box &box, mpq_class *actual_precision) {
  static IterationStats stat{DLINEAR_INFO_ENABLED, "QsoptexTheorySolver", "Total # of CheckSat",
                             "Total time spent in CheckSat"};
  TimerGuard check_sat_timer_guard(&stat.mutable_timer(), stat.enabled(), true /* start_timer */);
  stat.Increase();

  DLINEAR_TRACE_FMT("QsoptexTheorySolver::CheckSat: Box = \n{}", box);

  int status = -1;
  SatResult sat_status = SatResult::SAT_NO_RESULT;

  size_t rowcount = mpq_QSget_rowcount(qsx_);
  size_t colcount = mpq_QSget_colcount(qsx_);
  // x: * must be allocated/deallocated using QSopt_ex.
  //    * should have room for the (rowcount) "logical" variables, which come
  //    after the (colcount) "structural" variables.
  qsopt_ex::MpqArray x{colcount + rowcount};

  model_ = box;
  for (const std::pair<const int, Variable> &kv : theory_col_to_var_) {
    if (!model_.has_variable(kv.second)) {
      // Variable should already be present
      DLINEAR_WARN_FMT("QsoptexTheorySolver::CheckSat: Adding var {} to model from SAT", kv.second);
      model_.Add(kv.second);
    }
  }

  // The solver can't handle problems with inverted bounds, so we need to
  // handle that here.  Also, if there are no constraints, we can immediately
  // return SAT afterward if the bounds are OK.
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
    if (lb > ub) {
      DLINEAR_DEBUG_FMT("QsoptexTheorySolver::CheckSat: variable {} has invalid bounds [{}, {}]", var, lb, ub);
      return SatResult::SAT_UNSATISFIABLE;
    }
    if (rowcount == 0) {
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
  }
  mpq_clear(temp);
  if (rowcount == 0) {
    DLINEAR_DEBUG("QsoptexTheorySolver::CheckSat: no need to call LP solver");
    return SatResult::SAT_SATISFIABLE;
  }

  // Now we call the solver
  int lp_status = -1;
  DLINEAR_DEBUG_FMT("QsoptexTheorySolver::CheckSat: calling QSopt_ex (phase {})",
                    1 == simplex_sat_phase_ ? "one" : "two");

  if (1 == simplex_sat_phase_) {
    status =
        QSdelta_solver(qsx_, actual_precision->get_mpq_t(), static_cast<mpq_t *>(x), nullptr, nullptr, PRIMAL_SIMPLEX,
                       &lp_status, continuous_output_ ? QsoptexCheckSatPartialSolution : nullptr, this);
  } else {
    status = QSexact_delta_solver(qsx_, static_cast<mpq_t *>(x), nullptr, nullptr, PRIMAL_SIMPLEX, &lp_status,
                                  actual_precision->get_mpq_t(),
                                  continuous_output_ ? QsoptexCheckSatPartialSolution : nullptr, this);
  }

  if (status) {
    DLINEAR_RUNTIME_ERROR_FMT("QSopt_ex returned {}", status);
  } else {
    DLINEAR_DEBUG_FMT("QsoptexTheorySolver::CheckSat: QSopt_ex has returned with precision = {}", *actual_precision);
  }

  switch (lp_status) {
    case QS_LP_FEASIBLE:
      sat_status = SatResult::SAT_SATISFIABLE;
      break;
    case QS_LP_DELTA_FEASIBLE:
      sat_status = SatResult::SAT_DELTA_SATISFIABLE;
      break;
    case QS_LP_INFEASIBLE:
      sat_status = SatResult::SAT_UNSATISFIABLE;
      break;
    case QS_LP_UNSOLVED:
      sat_status = SatResult::SAT_UNSOLVED;
      DLINEAR_DEBUG("QsoptexTheorySolver::CheckSat: QSopt_ex failed to return a result");
      break;
    default:
      DLINEAR_UNREACHABLE();
  }

  switch (sat_status) {
    case SatResult::SAT_SATISFIABLE:
    case SatResult::SAT_DELTA_SATISFIABLE:
      // Copy delta-feasible point from x into model_
      for (const auto &[theory_col, var] : theory_col_to_var_) {
        DLINEAR_ASSERT(model_[var].lb() <= mpq_class(x[theory_col]) && mpq_class(x[theory_col]) <= model_[var].ub(),
                       "x[kv.first] must be in bounds");
        model_[var] = x[theory_col];
      }
      break;
    default:
      break;
  }

  return sat_status;
}

void QsoptexTheorySolver::Reset(const Box &box) {
  DLINEAR_TRACE_FMT("QsoptexTheorySolver::Reset(): Box =\n{}", box);
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

void QsoptexTheorySolver::SetQSXVarBound(const Variable &var, const char type, const mpq_class &value) {
  if (type == 'B') {
    // Both
    SetQSXVarBound(var, 'L', value);
    SetQSXVarBound(var, 'U', value);
    return;
  }
  DLINEAR_ASSERT(type == 'L' || type == 'U', "Type must be 'L' or 'U'");
  const auto it = var_to_theory_col_.find(var.get_id());
  if (it == var_to_theory_col_.end()) {
    DLINEAR_RUNTIME_ERROR_FMT("Variable undefined: {}", var);
  }
  if (value <= Infinity::Ninfty() || value >= Infinity::Infty()) {
    DLINEAR_RUNTIME_ERROR_FMT("Simple bound too large: {}", value);
  }
  mpq_t c_value;
  mpq_init(c_value);
  mpq_QSget_bound(qsx_, it->second, type, &c_value);
  mpq_class existing{c_value};
  if ((type == 'L' && existing < value) || (type == 'U' && value < existing)) {
    mpq_set(c_value, value.get_mpq_t());
    mpq_QSchange_bound(qsx_, it->second, type, c_value);
  }
  mpq_clear(c_value);
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

}  // namespace dlinear