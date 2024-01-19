//
// Created by c3054737 on 19/01/24.
//

#include "DeltaQsoptexTheorySolver.h"

#include <map>
#include <utility>

#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Infinity.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

DeltaQsoptexTheorySolver::DeltaQsoptexTheorySolver(PredicateAbstractor &predicate_abstractor, const Config &config)
    : QsoptexTheorySolver(predicate_abstractor, config) {}

void DeltaQsoptexTheorySolver::AddLiteral(const Literal &lit) {
  const auto &[formulaVar, truth] = lit;
  const auto &var_to_formula_map = predicate_abstractor_.var_to_formula_map();
  const auto it = var_to_formula_map.find(formulaVar);
  // Boolean variable - no need to involve theory solver
  if (it == var_to_formula_map.end()) return;

  const auto it2 = lit_to_theory_row_.find(formulaVar.get_id());
  // Found.
  if (it2 != lit_to_theory_row_.end()) return;

  // Theory formula
  const Formula &formula = it->second;
  // Create the LP solver variables
  for (const Variable &var : formula.GetFreeVariables()) {
    AddVariable(var);
  }
  if (IsEqualTo(formula, truth)) {
    // Just create simple bound in LP
    if (IsSimpleBound(formula)) return;
    qsx_sense_.push_back('E');
  } else if (IsGreaterThan(formula, truth) || IsGreaterThanOrEqualTo(formula, truth)) {
    // Just create simple bound in LP
    if (IsSimpleBound(formula)) return;
    qsx_sense_.push_back('G');
  } else if (IsLessThan(formula, truth) || IsLessThanOrEqualTo(formula, truth)) {
    // Just create simple bound in LP
    if (IsSimpleBound(formula)) return;
    qsx_sense_.push_back('L');
  } else if (IsNotEqualTo(formula, truth)) {
    // Nothing to do, because this constraint is always delta-sat for delta > 0.
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
  lit_to_theory_row_.emplace(formulaVar.get_id(), std::make_tuple(truth, qsx_row, -1));
  DLINEAR_ASSERT(static_cast<size_t>(qsx_row) == theory_row_to_lit_.size(), "Row count mismatch");
  theory_row_to_lit_.emplace_back(formulaVar, truth);
  DLINEAR_DEBUG_FMT("DeltaQsoptexTheorySolver::AddLinearLiteral({}{} ↦ {})", truth ? "" : "¬", it->second, qsx_row);
}

void DeltaQsoptexTheorySolver::EnableLiteral(const Literal &lit) {
  const auto &[var, truth] = lit;
  const auto it_row = lit_to_theory_row_.find(var.get_id());
  if (it_row != lit_to_theory_row_.end()) {
    // A non-trivial linear literal from the input problem
    const auto &[stored_truth, qsx_row, qsx_row2] = it_row->second;
    if (stored_truth == truth) {
      mpq_QSchange_sense(qsx_, qsx_row, qsx_sense_[qsx_row]);
      mpq_QSchange_rhscoef(qsx_, qsx_row, qsx_rhs_[qsx_row].get_mpq_t());
      DLINEAR_TRACE_FMT("DeltaQsoptexTheorySolver::EnableLinearLiteral({})", qsx_row);
      return;
    }
  }
  const auto &var_to_formula_map = predicate_abstractor_.var_to_formula_map();
  const auto it = var_to_formula_map.find(var);
  // Either a learned literal, or a not-equal literal from the input problem.
  if (it == var_to_formula_map.end() || !IsSimpleBound(it->second)) {
    DLINEAR_TRACE_FMT("DeltaQsoptexTheorySolver::EnableLinearLiteral: ignoring ({}, {})", var, truth);
    return;
  }

  // A simple bound - set it directly
  const Formula &formula{it->second};
  const Expression &lhs{get_lhs_expression(formula)};
  const Expression &rhs{get_rhs_expression(formula)};
  DLINEAR_TRACE_FMT("DeltaQsoptexTheorySolver::EnableLinearLiteral({}{})", truth ? "" : "¬", formula);
  if (IsEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) {
      SetQSXVarBound(get_variable(lhs), 'B', get_constant_value(rhs));
    } else if (is_constant(lhs) && is_variable(rhs)) {
      SetQSXVarBound(get_variable(rhs), 'B', get_constant_value(lhs));
    } else {
      DLINEAR_UNREACHABLE();
    }
  } else if (IsGreaterThan(formula, truth) || IsGreaterThanOrEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) {
      SetQSXVarBound(get_variable(lhs), 'L', get_constant_value(rhs));
    } else if (is_constant(lhs) && is_variable(rhs)) {
      SetQSXVarBound(get_variable(rhs), 'U', get_constant_value(lhs));
    } else {
      DLINEAR_UNREACHABLE();
    }
  } else if (IsLessThan(formula, truth) || IsLessThanOrEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) {
      SetQSXVarBound(get_variable(lhs), 'U', get_constant_value(rhs));
    } else if (is_constant(lhs) && is_variable(rhs)) {
      SetQSXVarBound(get_variable(rhs), 'L', get_constant_value(lhs));
    } else {
      DLINEAR_UNREACHABLE();
    }
  } else if (IsNotEqualTo(formula, truth)) {
    // Nothing to do, because this constraint is always delta-sat for delta > 0.
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
  }
}

SatResult DeltaQsoptexTheorySolver::CheckSat(const Box &box, mpq_class *actual_precision) {
  static IterationStats stat{DLINEAR_INFO_ENABLED, "DeltaQsoptexTheorySolver", "Total # of CheckSat",
                             "Total time spent in CheckSat"};
  TimerGuard check_sat_timer_guard(&stat.mutable_timer(), stat.enabled(), true /* start_timer */);
  stat.Increase();

  DLINEAR_TRACE_FMT("DeltaQsoptexTheorySolver::CheckSat: Box = \n{}", box);

  int status = -1;
  SatResult sat_status;

  size_t rowcount = mpq_QSget_rowcount(qsx_);
  size_t colcount = mpq_QSget_colcount(qsx_);
  // x: must be allocated/deallocated using QSopt_ex.
  // Should have room for the (rowcount) "logical" variables, which come fter the (colcount) "structural" variables.
  qsopt_ex::MpqArray x{colcount + rowcount};

  model_ = box;
  for (const std::pair<const int, Variable> &kv : theory_col_to_var_) {
    if (!model_.has_variable(kv.second)) {
      // Variable should already be present
      DLINEAR_WARN_FMT("DeltaQsoptexTheorySolver::CheckSat: Adding var {} to model from SAT", kv.second);
      model_.Add(kv.second);
    }
  }

  // The solver can't handle problems with inverted bounds, so we need to handle that here
  if (!CheckBounds()) return SatResult::SAT_UNSATISFIABLE;

  // If there are no constraints, we can immediately return SAT afterward
  if (rowcount == 0) {
    DLINEAR_DEBUG("DeltaQsoptexTheorySolver::CheckSat: no need to call LP solver");
    return SatResult::SAT_DELTA_SATISFIABLE;
  }

  // Now we call the solver
  int lp_status = -1;
  DLINEAR_DEBUG_FMT("DeltaQsoptexTheorySolver::CheckSat: calling QSopt_ex (phase {})",
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
    DLINEAR_DEBUG_FMT("DeltaQsoptexTheorySolver::CheckSat: QSopt_ex has returned with precision = {}",
                      *actual_precision);
  }

  switch (lp_status) {
    case QS_LP_FEASIBLE:
    case QS_LP_DELTA_FEASIBLE:
      sat_status = SatResult::SAT_DELTA_SATISFIABLE;
      break;
    case QS_LP_INFEASIBLE:
      sat_status = SatResult::SAT_UNSATISFIABLE;
      break;
    case QS_LP_UNSOLVED:
      sat_status = SatResult::SAT_UNSOLVED;
      DLINEAR_DEBUG("DeltaQsoptexTheorySolver::CheckSat: QSopt_ex failed to return a result");
      break;
    default:
      DLINEAR_UNREACHABLE();
  }

  switch (sat_status) {
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

}  // namespace dlinear
