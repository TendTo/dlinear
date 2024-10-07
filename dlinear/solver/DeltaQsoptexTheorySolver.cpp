/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "DeltaQsoptexTheorySolver.h"

#include <map>
#include <utility>

#include "dlinear/libs/libqsopt_ex.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

DeltaQsoptexTheorySolver::DeltaQsoptexTheorySolver(PredicateAbstractor &predicate_abstractor,
                                                   const std::string &class_name)
    : QsoptexTheorySolver(predicate_abstractor, class_name) {}

void DeltaQsoptexTheorySolver::AddLiteral(const Variable &formula_var, const Formula &formula) {
  DLINEAR_ASSERT(!is_consolidated_, "Cannot add literals after consolidation");
  // Literal is already present
  if (lit_to_theory_row_.contains(formula_var.get_id())) return;

  DLINEAR_TRACE_FMT("DeltaQsoptexTheorySolver::AddLiteral({})", formula);

  // Create the LP solver variables
  for (const Variable &var : formula.GetFreeVariables()) AddVariable(var);
  if (BoundPreprocessor::IsSimpleBound(formula)) return;

  const int qsx_row{mpq_QSget_rowcount(qsx_)};
  mpq_QSnew_row(qsx_, mpq_NINFTY, 'G', nullptr);
  SetRowCoeff(formula, mpq_QSget_rowcount(qsx_) - 1);
  qsx_sense_.emplace_back(~parseLpSense(formula));

  // Update indexes
  lit_to_theory_row_.emplace(formula_var.get_id(), qsx_row);
  theory_row_to_lit_.emplace_back(formula_var, true);

  DLINEAR_ASSERT(static_cast<std::size_t>(qsx_row) == theory_row_to_lit_.size() - 1,
                 "incorrect theory_row_to_lit_.size()");
  DLINEAR_ASSERT(static_cast<std::size_t>(qsx_row) == qsx_sense_.size() - 1, "incorrect spx_sense_.size()");
  DLINEAR_ASSERT(static_cast<std::size_t>(qsx_row) == qsx_rhs_.size() - 1, "incorrect spx_rhs_.size()");
  DLINEAR_DEBUG_FMT("DeltaQsoptexTheorySolver::AddLiteral: {} ↦ {}", formula, qsx_row);
}

DeltaQsoptexTheorySolver::Explanations DeltaQsoptexTheorySolver::EnableLiteral(const Literal &lit) {
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");
  DLINEAR_ASSERT(predicate_abstractor_.var_to_formula_map().contains(lit.var), "var must map to a theory literal");

  Explanations explanations{preprocessor_.EnableLiteral(lit)};
  if (!explanations.empty()) return explanations;

  const auto &[var, truth] = lit;
  const auto it = lit_to_theory_row_.find(var.get_id());
  // If the literal was not already among the constraints (rows) of the LP, it must be a learned literal.
  if (it == lit_to_theory_row_.end()) {
    DLINEAR_TRACE_FMT("DeltaQsoptexTheorySolver::EnableLinearLiteral: ignoring ({})", lit);
    return {};
  }

  // A non-trivial linear literal from the input problem
  const int qsx_row = it->second;
  // Update the truth value for the current iteration with the last SAT solver assignment
  theory_row_to_lit_[qsx_row].truth = truth;

  DLINEAR_TRACE_FMT("DeltaQsoptexTheorySolver::EnableLinearLiteral({})", lit);

  EnableQsxRow(qsx_row, truth);
  return explanations;
}

SatResult DeltaQsoptexTheorySolver::CheckSatCore(mpq_class *actual_precision, Explanations &explanations) {
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before checking for sat");

  int status = -1;

  const std::size_t rowcount = mpq_QSget_rowcount(qsx_);
  const std::size_t colcount = mpq_QSget_colcount(qsx_);
  // x: must be allocated/deallocated using QSopt_ex.
  // Should have room for the (rowcount) "logical" variables, which come after the (colcount) "structural" variables.
  x_.Resize(colcount + rowcount);
  ray_.Resize(rowcount);

  // Set the bounds for the variables
  EnableQsxVarBound();
  // Remove all the disabled rows from the LP solver
  DisableQsxRows();

  // Now we call the solver
  int lp_status = -1;
  DLINEAR_DEBUG_FMT("DeltaQsoptexTheorySolver::CheckSat: calling QSopt_ex (phase {})", config_.simplex_sat_phase());

  if (1 == config_.simplex_sat_phase()) {
    status = QSdelta_solver(qsx_, actual_precision->get_mpq_t(), static_cast<mpq_t *>(x_), static_cast<mpq_t *>(ray_),
                            nullptr, PRIMAL_SIMPLEX, &lp_status,
                            config_.continuous_output() ? QsoptexCheckSatPartialSolution : nullptr, this);
  } else {
    status = QSexact_delta_solver(qsx_, static_cast<mpq_t *>(x_), static_cast<mpq_t *>(ray_), nullptr, PRIMAL_SIMPLEX,
                                  &lp_status, actual_precision->get_mpq_t(),
                                  config_.continuous_output() ? QsoptexCheckSatPartialSolution : nullptr, this);
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
      UpdateModelSolution();
      DLINEAR_DEBUG("DeltaQsoptexTheorySolver::CheckSat: returning SAT_DELTA_SATISFIABLE");
      return SatResult::SAT_DELTA_SATISFIABLE;
    case QS_LP_INFEASIBLE:
      UpdateExplanations(explanations);
      DLINEAR_DEBUG("DeltaQsoptexTheorySolver::CheckSat: returning SAT_UNSATISFIABLE");
      return SatResult::SAT_UNSATISFIABLE;
    case QS_LP_UNSOLVED:
      DLINEAR_WARN("DeltaQsoptexTheorySolver::CheckSat: QSopt_ex failed to return a result");
      return SatResult::SAT_UNSOLVED;
    default:
      DLINEAR_UNREACHABLE();
  }
}

void DeltaQsoptexTheorySolver::EnableQsxRow(int qsx_row, bool truth) {
  const LpRowSense sense = qsx_sense_[qsx_row];
  mpq_class &rhs{qsx_rhs_[qsx_row]};
  char qsx_sense;
  if (truth) {
    if (sense == LpRowSense::NQ) return;
    qsx_sense = toChar(sense);
  } else {
    if (sense == LpRowSense::EQ) return;
    qsx_sense = toChar(-sense);
  }
  mpq_QSchange_sense(qsx_, qsx_row, qsx_sense);
  mpq_QSchange_rhscoef(qsx_, qsx_row, rhs.get_mpq_t());
  theory_rows_state_.at(qsx_row) = true;
  DLINEAR_TRACE_FMT("DeltaQsoptexTheorySolver::EnableLinearLiteral({}{})", truth ? "" : "¬", qsx_row);
}

}  // namespace dlinear
