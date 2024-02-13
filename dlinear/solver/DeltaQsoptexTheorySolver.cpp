/**
 * @file DeltaQsoptexTheorySolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
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
  // Literal is already present
  if (it2 != lit_to_theory_row_.end()) return;

  // Theory formula
  const Formula &formula = it->second;
  // Create the LP solver variables
  for (const Variable &var : formula.GetFreeVariables()) AddVariable(var);

  // Just create simple bound in LP
  // It will be handled when enabling the literal
  if (IsSimpleBound(formula)) return;

  if (IsEqualTo(formula, truth)) {
    qsx_sense_.push_back(LpRowSense::EQ);
  } else if (IsGreaterThan(formula, truth) || IsGreaterThanOrEqualTo(formula, truth)) {
    qsx_sense_.push_back(LpRowSense::GE);
  } else if (IsLessThan(formula, truth) || IsLessThanOrEqualTo(formula, truth)) {
    qsx_sense_.push_back(LpRowSense::LE);
  } else if (IsNotEqualTo(formula, truth)) {
    // The constraint, because this constraint is always delta-sat for delta > 0.
    qsx_sense_.push_back(LpRowSense::NQ);
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
  }

  Expression expr = (get_lhs_expression(formula) - get_rhs_expression(formula)).Expand();
  const int qsx_row{mpq_QSget_rowcount(qsx_)};
  // Add inactive constraint
  mpq_QSnew_row(qsx_, mpq_NINFTY, 'G', nullptr);
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
  lit_to_theory_row_.emplace(formulaVar.get_id(), std::pair(qsx_row, -1));
  DLINEAR_ASSERT(static_cast<size_t>(qsx_row) == theory_row_to_lit_.size(), "Row count mismatch");
  theory_row_to_lit_.emplace_back(formulaVar);
  theory_row_to_truth_.push_back(truth);
  DLINEAR_DEBUG_FMT("DeltaQsoptexTheorySolver::AddLinearLiteral({}{} ↦ {})", truth ? "" : "¬", it->second, qsx_row);
}

std::optional<LiteralSet> DeltaQsoptexTheorySolver::EnableLiteral(const Literal &lit) {
  const auto &[var, truth] = lit;
  const auto it_row = lit_to_theory_row_.find(var.get_id());
  if (it_row != lit_to_theory_row_.end()) {
    // A non-trivial linear literal from the input problem
    const auto &[qsx_row, qsx_row2] = it_row->second;

    const LpRowSense row_sense = qsx_sense_[qsx_row];
    mpq_class &rhs{qsx_rhs_[qsx_row]};
    char sense;
    if (truth) {
      if (row_sense == LpRowSense::NQ) return {};
      sense = toChar(row_sense);
    } else {
      if (row_sense == LpRowSense::EQ) return {};
      sense = toChar(~row_sense);
    }
    mpq_QSchange_sense(qsx_, qsx_row, sense);
    mpq_QSchange_rhscoef(qsx_, qsx_row, rhs.get_mpq_t());
    theory_row_to_truth_[qsx_row] = truth;
    DLINEAR_TRACE_FMT("DeltaQsoptexTheorySolver::EnableLinearLiteral({}{})", truth ? "" : "¬", qsx_row);
    return {};
  }

  // If the literal was not already among the constraints (rows) of the LP, it must be a bound
  // on a variable (column) or a learned literal.
  const auto &it = predicate_abstractor_.var_to_formula_map().find(var);
  // The variable is not in the map (it is not a theory literal) or it is not a simple bound
  if (it == predicate_abstractor_.var_to_formula_map().end() || !IsSimpleBound(it->second)) {
    DLINEAR_TRACE_FMT("DeltaQsoptexTheorySolver::EnableLinearLiteral: ignoring ({}, {})", var, truth);
    return {};
  }

  // A simple bound - set it directly
  DLINEAR_TRACE_FMT("DeltaQsoptexTheorySolver::EnableLinearLiteral({}{})", truth ? "" : "¬", it->second);
  // bound = (variable, type, value), where:
  // - variable is the box variable
  // - type is 'L' for lower bound, 'U' for upper bound, 'B' for both, 'F' for free
  // - value is the bound value
  Bound bound = GetBound(it->second, truth);
  // If the bound type is 'I' or 'N' (delta > 0), we can just ignore the bound
  if (std::get<1>(bound) == LpColBound::F) return {};

  // Add the active bound to the LP solver bounds
  int theory_col = var_to_theory_col_[std::get<0>(bound).get_id()];
  bool valid_bound = SetQSXVarBound(bound, theory_col);
  theory_bound_to_explanation_[theory_col].insert(lit);
  if (!valid_bound) return theory_bound_to_explanation_[theory_col];
  return {};
}

SatResult DeltaQsoptexTheorySolver::CheckSat(const Box &box, mpq_class *actual_precision, LiteralSet &explanation) {
  static IterationStats stat{DLINEAR_INFO_ENABLED, "DeltaQsoptexTheorySolver", "Total # of CheckSat",
                             "Total time spent in CheckSat"};
  TimerGuard check_sat_timer_guard(&stat.m_timer(), stat.enabled(), true /* start_timer */);
  stat.Increase();

  DLINEAR_TRACE_FMT("DeltaQsoptexTheorySolver::CheckSat: Box = \n{}", box);

  int status = -1;
  SatResult sat_status;

  size_t rowcount = mpq_QSget_rowcount(qsx_);
  size_t colcount = mpq_QSget_colcount(qsx_);
  // x: must be allocated/deallocated using QSopt_ex.
  // Should have room for the (rowcount) "logical" variables, which come after the (colcount) "structural" variables.
  qsopt_ex::MpqArray x{colcount + rowcount};
  qsopt_ex::MpqArray y{rowcount};

  model_ = box;
  for (const auto &var : theory_col_to_var_) {
    if (!model_.has_variable(var)) {
      // Variable should already be present
      DLINEAR_WARN_FMT("DeltaQsoptexTheorySolver::CheckSat: Adding var {} to model from SAT", var);
      model_.Add(var);
    }
  }

  // If there are no constraints, we can immediately return SAT afterward
  if (rowcount == 0) {
    DLINEAR_DEBUG("DeltaQsoptexTheorySolver::CheckSat: no need to call LP solver");
    UpdateModelBounds();
    return SatResult::SAT_DELTA_SATISFIABLE;
  }

  // Now we call the solver
  int lp_status = -1;
  DLINEAR_DEBUG_FMT("DeltaQsoptexTheorySolver::CheckSat: calling QSopt_ex (phase {})",
                    1 == simplex_sat_phase_ ? "one" : "two");

  if (1 == simplex_sat_phase_) {
    status =
        QSdelta_solver(qsx_, actual_precision->get_mpq_t(), static_cast<mpq_t *>(x), static_cast<mpq_t *>(y), nullptr,
                       PRIMAL_SIMPLEX, &lp_status, continuous_output_ ? QsoptexCheckSatPartialSolution : nullptr, this);
  } else {
    status = QSexact_delta_solver(qsx_, static_cast<mpq_t *>(x), static_cast<mpq_t *>(y), nullptr, PRIMAL_SIMPLEX,
                                  &lp_status, actual_precision->get_mpq_t(),
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
      UpdateExplanation(y, explanation);
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
      for (int theory_col = 0; theory_col < static_cast<int>(theory_col_to_var_.size()); theory_col++) {
        const Variable &var{theory_col_to_var_[theory_col]};
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
