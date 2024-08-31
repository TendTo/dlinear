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
    : SoplexTheorySolver(predicate_abstractor, class_name) {
  DLINEAR_ASSERT(config_.simplex_sat_phase() == 1, "DeltaSoplexTheorySolver must use phase 1");
}

void DeltaSoplexTheorySolver::AddLiteral(const Variable &formula_var, const Formula &formula) {
  if (is_consolidated_) DLINEAR_RUNTIME_ERROR("Cannot add literals after consolidation");
  const auto it = lit_to_theory_row_.find(formula_var.get_id());
  // Literal is already present
  if (it != lit_to_theory_row_.end()) return;

  // Create the LP solver variables
  for (const Variable &var : formula.GetFreeVariables()) AddVariable(var);

  spx_sense_.emplace_back(~parseLpSense(formula));
  DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::AddLinearLiteral: {} -> {}", formula_var, spx_sense_.back());

  const int spx_row{spx_.numRowsRational()};

  const bool is_simple_bound = BoundPreprocessor::IsSimpleBound(formula);
  soplex::DSVectorRational coeffs{is_simple_bound ? soplex::DSVectorRational{} : ParseRowCoeff(formula)};
  if (is_simple_bound) spx_rhs_.emplace_back(0);
  spx_.addRowRational(soplex::LPRowRational(-soplex::infinity, coeffs, soplex::infinity));

  // Update indexes
  lit_to_theory_row_.emplace(formula_var.get_id(), spx_row);
  theory_row_to_lit_.emplace_back(formula_var, true);

  DLINEAR_ASSERT(static_cast<std::size_t>(spx_row) == theory_row_to_lit_.size() - 1,
                 "incorrect theory_row_to_lit_.size()");
  DLINEAR_ASSERT(static_cast<std::size_t>(spx_row) == spx_sense_.size() - 1, "incorrect spx_sense_.size()");
  DLINEAR_ASSERT(static_cast<std::size_t>(spx_row) == spx_rhs_.size() - 1, "incorrect spx_rhs_.size()");
  DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::AddLinearLiteral({} ↦ {})", formula_var, spx_row);
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

  Explanations explanations{preprocessor_.EnableLiteral(lit)};
  if (!explanations.empty()) return explanations;

  // If it is not a simple bound, we need to enable the row in the soplex solver
  if (!BoundPreprocessor::IsSimpleBound(formula)) EnableSpxRow(spx_row, truth);
  return explanations;
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

  preprocessor_.Process(explanations);
  if (!explanations.empty()) return SatResult::SAT_UNSATISFIABLE;
  DLINEAR_ERROR("CompleteSoplexTheorySolver::CheckSat: running soplex");

  // Set the bounds for the variables
  EnableSPXVarBound();
  // Remove all the disabled rows from the LP solver
  DisableSpxRows();

  // Now we call the solver
  DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::CheckSat: calling SoPlex (phase {})", config_.simplex_sat_phase());

  Rational max_violation, sum_violation;

  status = spx_.optimize();

  // The status must be OPTIMAL, UNBOUNDED, or INFEASIBLE. Anything else is an error
  if (status != SoplexStatus::OPTIMAL && status != SoplexStatus::UNBOUNDED && status != SoplexStatus::INFEASIBLE) {
    DLINEAR_RUNTIME_ERROR_FMT("SoPlex returned {}. That's not allowed here", status);
  } else if (spx_.getRowViolationRational(max_violation, sum_violation)) {
    *actual_precision = max_violation.convert_to<mpq_class>();
    DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::CheckSat: SoPlex returned {}, precision = {}", status,
                      *actual_precision);
  } else {
    DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::CheckSat: SoPlex has returned {}, but no precision", status);
  }

  switch (status) {
    case SoplexStatus::OPTIMAL:
      UpdateModelSolution();
      sat_status = SatResult::SAT_DELTA_SATISFIABLE;
      break;
    case SoplexStatus::INFEASIBLE:
      UpdateExplanations(explanations);
      sat_status = SatResult::SAT_UNSATISFIABLE;
      break;
    default:
      DLINEAR_UNREACHABLE();
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
