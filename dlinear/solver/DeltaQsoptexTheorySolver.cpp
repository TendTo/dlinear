/**
 * @file DeltaQsoptexTheorySolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "DeltaQsoptexTheorySolver.h"

#include <map>
#include <utility>

#include "dlinear/libs/libqsopt_ex.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Infinity.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

DeltaQsoptexTheorySolver::DeltaQsoptexTheorySolver(PredicateAbstractor &predicate_abstractor,
                                                   const std::string &class_name)
    : QsoptexTheorySolver(predicate_abstractor, class_name) {}

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
  lit_to_theory_row_.emplace(formulaVar.get_id(), qsx_row);
  DLINEAR_ASSERT(static_cast<size_t>(qsx_row) == theory_row_to_lit_.size(), "Row count mismatch");
  theory_row_to_lit_.push_back(lit);
  DLINEAR_DEBUG_FMT("DeltaQsoptexTheorySolver::AddLinearLiteral({} ↦ {})", lit, qsx_row);
}

DeltaQsoptexTheorySolver::Explanations DeltaQsoptexTheorySolver::EnableLiteral(const Literal &lit) {
  Consolidate();
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");

  const auto &[var, truth] = lit;
  const auto it_row = lit_to_theory_row_.find(var.get_id());
  if (it_row != lit_to_theory_row_.end()) {
    // A non-trivial linear literal from the input problem
    const int qsx_row = it_row->second;

    const LpRowSense row_sense = qsx_sense_[qsx_row];
    mpq_class &rhs{qsx_rhs_[qsx_row]};
    char sense;
    if (truth) {
      if (row_sense == LpRowSense::NQ) return {};
      sense = toChar(row_sense);
    } else {
      if (row_sense == LpRowSense::EQ) return {};
      sense = toChar(-row_sense);
    }
    mpq_QSchange_sense(qsx_, qsx_row, sense);
    mpq_QSchange_rhscoef(qsx_, qsx_row, rhs.get_mpq_t());
    theory_row_to_lit_[qsx_row].truth = truth;
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

  DLINEAR_RUNTIME_ERROR("Needs to be fixed properly. Look at DeltaSoplexTheorySolver::EnableLiteral for reference.");
  int qsx_row = mpq_QSget_rowcount(qsx_);
  // A simple bound - set it directly
  DLINEAR_TRACE_FMT("DeltaQsoptexTheorySolver::EnableLinearLiteral({}{})", truth ? "" : "¬", it->second);
  // bound = (variable, type, value), where:
  // - variable is the box variable
  // - type is 'L' for lower bound, 'U' for upper bound, 'B' for both, 'F' for free
  // - value is the bound value
  auto [b_var, type, value] = GetBound(it->second, truth);
  // Since delta > 0, we can relax the bound type
  type = ~type;
  // If the bound is now free, there is no need to consider it
  if (type == LpColBound::F) return {};

  // Add the active bound to the LP solver bounds
  const int theory_col = var_to_theory_col_.at(b_var.get_id());
  const TheorySolverBoundVector::BoundIterator violation{theory_bounds_[theory_col].AddBound(value, type, qsx_row)};
  // If the bound is invalid, return the explanation and update the SAT solver immediately
  if (violation) return TheoryBoundsToExplanations(violation, qsx_row);
  return {};
}

SatResult DeltaQsoptexTheorySolver::CheckSat(const Box &box, mpq_class *actual_precision, Explanations &explanations) {
  Consolidate();
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");

  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();

  DLINEAR_TRACE_FMT("DeltaQsoptexTheorySolver::CheckSat: Box = \n{}", box);

  int status = -1;
  SatResult sat_status = SatResult::SAT_NO_RESULT;

  size_t rowcount = mpq_QSget_rowcount(qsx_);
  size_t colcount = mpq_QSget_colcount(qsx_);
  // x: must be allocated/deallocated using QSopt_ex.
  // Should have room for the (rowcount) "logical" variables, which come after the (colcount) "structural" variables.
  qsopt_ex::MpqArray x{colcount + rowcount};
  ray_.Resize(rowcount);

  model_ = box;
  DLINEAR_ASSERT(std::all_of(theory_col_to_var_.begin(), theory_col_to_var_.end(),
                             [&box](const Variable &var) { return box.has_variable(var); }),
                 "All theory variables must be present in the box");

  // If there are no constraints, we can immediately return SAT afterward
  if (rowcount == 0) {
    DLINEAR_DEBUG("DeltaQsoptexTheorySolver::CheckSat: no need to call LP solver");
    UpdateModelBounds();
    return SatResult::SAT_DELTA_SATISFIABLE;
  }

  // Set the bounds for the variables
  SetQPXVarBound();

  // Now we call the solver
  int lp_status = -1;
  DLINEAR_DEBUG_FMT("DeltaQsoptexTheorySolver::CheckSat: calling QSopt_ex (phase {})", config_.simplex_sat_phase());

  if (1 == config_.simplex_sat_phase()) {
    status = QSdelta_solver(qsx_, actual_precision->get_mpq_t(), static_cast<mpq_t *>(x), static_cast<mpq_t *>(ray_),
                            nullptr, PRIMAL_SIMPLEX, &lp_status,
                            continuous_output_ ? QsoptexCheckSatPartialSolution : nullptr, this);
  } else {
    status = QSexact_delta_solver(qsx_, static_cast<mpq_t *>(x), static_cast<mpq_t *>(ray_), nullptr, PRIMAL_SIMPLEX,
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
      UpdateExplanations(explanations);
      break;
    case QS_LP_UNSOLVED:
      sat_status = SatResult::SAT_UNSOLVED;
      DLINEAR_WARN("DeltaQsoptexTheorySolver::CheckSat: QSopt_ex failed to return a result");
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
