/**
 * @file DeltaSoplexTheorySolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "DeltaSoplexTheorySolver.h"

#include <algorithm>
#include <cstddef>
#include <map>
#include <unordered_map>
#include <utility>
#include <vector>

#include "dlinear/libs/libsoplex.h"
#include "dlinear/solver/LpColBound.h"
#include "dlinear/solver/LpRowSense.h"
#include "dlinear/solver/TheorySolverBoundVector.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

using SoplexStatus = soplex::SPxSolver::Status;
using soplex::Rational;

DeltaSoplexTheorySolver::DeltaSoplexTheorySolver(PredicateAbstractor &predicate_abstractor,
                                                 const std::string &class_name)
    : SoplexTheorySolver(predicate_abstractor, class_name) {}

void DeltaSoplexTheorySolver::AddLiteral(const Literal &lit) {
  if (is_consolidated_) DLINEAR_RUNTIME_ERROR("Cannot add literals after consolidation");
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

  if (IsEqualTo(formula)) {
    spx_sense_.push_back(LpRowSense::EQ);
  } else if (IsGreaterThan(formula) || IsGreaterThanOrEqualTo(formula)) {
    spx_sense_.push_back(LpRowSense::GE);
  } else if (IsLessThan(formula) || IsLessThanOrEqualTo(formula)) {
    spx_sense_.push_back(LpRowSense::LE);
  } else if (IsNotEqualTo(formula)) {
    // This constraint will be ignored, because it is always delta-sat for delta > 0.
    spx_sense_.push_back(LpRowSense::NQ);
  } else {
    DLINEAR_UNREACHABLE();
  }
  DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::AddLinearLiteral: {} -> {}", lit, spx_sense_.back());

  const int spx_row{spx_.numRowsRational()};

  // TODO: add preprocessor
  soplex::DSVectorRational coeffs{IsSimpleBound(formula) ? soplex::DSVectorRational{} : ParseRowCoeff(formula)};
  if (IsSimpleBound(formula)) spx_rhs_.emplace_back(0);
  spx_.addRowRational(soplex::LPRowRational(-soplex::infinity, coeffs, soplex::infinity));
  if (2 == config_.simplex_sat_phase()) CreateArtificials(spx_row);

  // Update indexes
  lit_to_theory_row_.emplace(formulaVar.get_id(), spx_row);
  theory_row_to_lit_.emplace_back(formulaVar, true);

  DLINEAR_ASSERT(static_cast<std::size_t>(spx_row) == theory_row_to_lit_.size() - 1,
                 "incorrect theory_row_to_lit_.size()");
  DLINEAR_ASSERT(static_cast<std::size_t>(spx_row) == spx_sense_.size() - 1, "incorrect spx_sense_.size()");
  DLINEAR_ASSERT(static_cast<std::size_t>(spx_row) == spx_rhs_.size() - 1, "incorrect spx_rhs_.size()");
  DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::AddLinearLiteral({} ↦ {})", lit, spx_row);
}

DeltaSoplexTheorySolver::Explanations DeltaSoplexTheorySolver::EnableLiteral(const Literal &lit) {
  Consolidate();
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");

  const auto &[var, truth] = lit;
  const auto it_row = lit_to_theory_row_.find(var.get_id());

  // If the literal was not already among the constraints (rows) of the LP, it must be a learned literal.
  if (it_row == lit_to_theory_row_.end()) {
    DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::EnableLinearLiteral: ignoring ({}{})", truth ? "" : "¬", var);
    return {};
  }

  // A non-trivial linear literal from the input problem
  const int spx_row = it_row->second;
  // Update the truth value for the current iteration with the last SAT solver assignment
  theory_row_to_lit_[spx_row].truth = truth;
  // Add the row to the list of enabled theory rows
  enabled_theory_rows_.push_back(spx_row);

  DLINEAR_ASSERT(predicate_abstractor_.var_to_formula_map().count(var) != 0, "var must map to a theory literal");
  const Formula &formula = predicate_abstractor_[var];
  DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::EnableLinearLiteral({}{})", truth ? "" : "¬", formula);

  // If it is a simple bound, we add it to the theory_bounds.
  if (IsSimpleBound(formula)) {
    // bound = (variable, type, value), where:
    // - variable is the box variable
    // - type of bound
    // - value is the bound value
    auto [b_var, type, value] = GetBound(formula, truth);
    type = ~type;
    DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::EnableLinearLiteral: bound ({}, {} {})", b_var, type, value);
    // If the bound is now free, there is no need to consider it
    if (type == LpColBound::F) return {};

    // Add the active bound to the LP solver bounds
    int theory_col = var_to_theory_col_[b_var.get_id()];
    const TheorySolverBoundVector::BoundIterator violation{theory_bounds_[theory_col].AddBound(value, type, spx_row)};

    // If the bound is invalid, return the explanation and update the SAT solver immediately
    if (violation) return TheoryBoundsToExplanations(violation, spx_row);
    return {};
  }

  EnableSpxRow(spx_row, truth);
  return {};
}

SatResult DeltaSoplexTheorySolver::CheckSat(const Box &box, mpq_class *actual_precision, Explanations &explanations) {
  Consolidate();
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");

  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();

  DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::CheckSat: Box = \n{}", box);

  SoplexStatus status = SoplexStatus::UNKNOWN;
  SatResult sat_status = SatResult::SAT_NO_RESULT;

  int rowcount = spx_.numRowsRational();
  int colcount = spx_.numColsRational();

  model_ = box;
  DLINEAR_ASSERT(std::all_of(theory_col_to_var_.begin(), theory_col_to_var_.end(),
                             [&box](const Variable &var) { return box.has_variable(var); }),
                 "All theory variables must be present in the box");

  // If we can immediately return SAT afterward
  if (rowcount == 0) {
    DLINEAR_DEBUG("DeltaSoplexTheorySolver::CheckSat: no need to call LP solver");
    UpdateModelBounds();
    return SatResult::SAT_DELTA_SATISFIABLE;
  }

  // Set the bounds for the variables
  EnableSPXVarBound();
  // Remove all the disabled rows from the LP solver
  DisableSpxRows();

  // Now we call the solver
  DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::CheckSat: calling SoPlex (phase {})", config_.simplex_sat_phase());

  Rational max_violation, sum_violation;

  status = spx_.optimize();

  // If the simplex_sat_status is 2, we expect the status to be OPTIMAL
  // Otherwise, the status must be OPTIMAL, UNBOUNDED, or INFEASIBLE
  // Anything else is an error
  if ((2 == config_.simplex_sat_phase() && status != SoplexStatus::OPTIMAL) ||
      (status != SoplexStatus::OPTIMAL && status != SoplexStatus::UNBOUNDED && status != SoplexStatus::INFEASIBLE)) {
    DLINEAR_RUNTIME_ERROR_FMT("SoPlex returned {}. That's not allowed here", status);
  } else if (spx_.getRowViolationRational(max_violation, sum_violation)) {
    *actual_precision = max_violation.convert_to<mpq_class>();
    DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::CheckSat: SoPlex returned {}, precision = {}", status,
                      *actual_precision);
  } else {
    DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::CheckSat: SoPlex has returned {}, but no precision", status);
  }

  soplex::VectorRational x;
  x.reDim(colcount);
  bool has_sol = spx_.getPrimalRational(x);
  if (has_sol && x.dim() != colcount) {
    DLINEAR_ASSERT(x.dim() >= colcount, "x.dim() must be >= colcount");
    DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::CheckSat: colcount = {} but x.dim() = {} after getPrimalRational()",
                      colcount, x.dim());
  }
  DLINEAR_ASSERT(status != SoplexStatus::OPTIMAL || has_sol,
                 "status must either be not OPTIMAL or a solution must be present");

  if (1 == config_.simplex_sat_phase()) {
    switch (status) {
      case SoplexStatus::OPTIMAL:
        sat_status = SatResult::SAT_DELTA_SATISFIABLE;
        break;
      case SoplexStatus::INFEASIBLE:
        sat_status = SatResult::SAT_UNSATISFIABLE;
        UpdateExplanations(explanations);
        break;
      default:
        DLINEAR_UNREACHABLE();
    }
  } else {
    // The feasibility LP should always be feasible & bounded
    DLINEAR_ASSERT(status == SoplexStatus::OPTIMAL, "status must be OPTIMAL");
    soplex::VectorRational obj;
    spx_.getObjRational(obj);
    DLINEAR_ASSERT(obj.dim() == colcount, "obj.dim() must be == colcount");
    bool ok = true;
    // ok = std::ranges::all_of(0, colcount, [&] (int i) { return obj[i] == 0 || x[i] == 0; });
    for (int i = 0; i < colcount; ++i) {
      if (!(ok = (obj[i] == 0 || x[i] == 0))) {
        break;
      }
    }
    if (ok) {
      sat_status = SatResult::SAT_DELTA_SATISFIABLE;
    } else {
      sat_status = SatResult::SAT_UNSATISFIABLE;
    }
  }

  switch (sat_status) {
    case SatResult::SAT_DELTA_SATISFIABLE:
      DLINEAR_ASSERT(has_sol, "has_sol must be true");
      // Copy delta-feasible point from x into model_
      for (int theory_col = 0; theory_col < static_cast<int>(theory_col_to_var_.size()); theory_col++) {
        const Variable &var{theory_col_to_var_[theory_col]};
        DLINEAR_ASSERT(model_[var].lb() <= gmp::to_mpq_class(x[theory_col].backend().data()) &&
                           gmp::to_mpq_class(x[theory_col].backend().data()) <= model_[var].ub(),
                       "val must be in bounds");
        model_[var] = x[theory_col].backend().data();
      }
      break;
    default:
      break;
  }
  DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::CheckSat: returning {}", sat_status);

  return sat_status;
}

void DeltaSoplexTheorySolver::EnableSpxRow(int spx_row, bool truth) {
  const LpRowSense sense = spx_sense_[spx_row];
  const mpq_class &rhs{spx_rhs_[spx_row]};
  if (truth) {
    if (sense == LpRowSense::NQ) return;
    spx_.changeRangeRational(
        spx_row,
        sense == LpRowSense::GE || sense == LpRowSense::EQ ? Rational(gmp::to_mpq_t(rhs)) : Rational(-soplex::infinity),
        sense == LpRowSense::LE || sense == LpRowSense::EQ ? Rational(gmp::to_mpq_t(rhs)) : Rational(soplex::infinity));
  } else {
    if (sense == LpRowSense::EQ) return;
    spx_.changeRangeRational(
        spx_row,
        sense == LpRowSense::LE || sense == LpRowSense::NQ ? Rational(gmp::to_mpq_t(rhs)) : Rational(-soplex::infinity),
        sense == LpRowSense::GE || sense == LpRowSense::NQ ? Rational(gmp::to_mpq_t(rhs)) : Rational(soplex::infinity));
  }
  theory_rows_state_.at(spx_row) = true;
  DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::EnableLinearLiteral({}{})", truth ? "" : "¬", spx_row);
}

}  // namespace dlinear
