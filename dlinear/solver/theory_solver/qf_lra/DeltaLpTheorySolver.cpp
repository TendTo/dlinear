/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "DeltaLpTheorySolver.h"

#include "dlinear/solver/theory_solver/qf_lra/BoundPreprocessor.h"
#include "dlinear/util/error.h"

namespace dlinear {

DeltaLpTheorySolver::DeltaLpTheorySolver(const PredicateAbstractor& predicate_abstractor, const std::string& class_name)
    : LpTheorySolver{predicate_abstractor, class_name} {}

void DeltaLpTheorySolver::AddLiteral(const Variable& formula_var, const Formula& formula) {
  DLINEAR_ASSERT(!is_consolidated_, "Cannot add literals after consolidation");
  // Literal is already present
  if (lp_solver_->lit_to_row().contains(formula_var)) return;

  DLINEAR_TRACE_FMT("DeltaLpTheorySolver::AddLiteral({})", formula);

  // Create the LP solver variables
  for (const Variable& var : formula.GetFreeVariables()) AddVariable(var);
  if (BoundPreprocessor::IsSimpleBound(formula)) return;

  lp_solver_->AddRow(formula_var, formula, ~parseLpSense(formula));

  DLINEAR_DEBUG_FMT("DeltaLpTheorySolver::AddLiteral: {} ↦ {}", formula, lp_solver_->num_rows());
}

bool DeltaLpTheorySolver::EnableLiteral(const Literal& lit, const ConflictCallback& conflict_cb) {
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");
  DLINEAR_ASSERT(pa_.var_to_formula_map().contains(lit.var), "var must map to a theory literal");
  // No need to enable a fixed literal again
  if (enabled_literals_checkpoint_.contains(lit.var)) return true;

  if (preprocessor_ != nullptr) {
    const bool success = preprocessor_->EnableLiteral(lit, conflict_cb);
    if (!success) return false;
  }

  const auto& [var, truth] = lit;
  const auto it = lp_solver_->lit_to_row().find(var);
  // If the literal is not among the constraints (rows) of the LP, it must be a simple bound.
  if (it == lp_solver_->lit_to_row().end()) {
    DLINEAR_TRACE_FMT("DeltaLpTheorySolver::EnableLinearLiteral: enabling simple bound ({})", lit);
    const Formula& formula = pa_[lit.var];
    const bool added = vars_bounds_.at(*formula.GetFreeVariables().cbegin())
                           .AddBound(BoundPreprocessor::GetSimpleBound(lit, formula), conflict_cb);
    if (!added) DLINEAR_TRACE_FMT("DeltaLpTheorySolver::EnableLinearLiteral: failed to add simple bound ({})", lit);
    return added;
  }

  // A non-trivial linear literal from the input problem
  const int row = it->second;
  // Update the truth value for the current iteration with the last SAT solver assignment
  lp_solver_->UpdateLiteralAssignment(row, truth);
  lp_solver_->EnableRow(row, truth ? lp_solver_->senses()[row] : -lp_solver_->senses()[row]);

  // Set the row as enabled
  rows_state_.at(row) = true;

  DLINEAR_TRACE_FMT("DeltaLpTheorySolver::EnableLinearLiteral({})", lit);
  return true;
}

TheoryResult DeltaLpTheorySolver::CheckSatCore(mpq_class* actual_precision, const ConflictCallback& conflict_cb) {
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before checking for sat");

  // There are no rows in the LP problem, only bounds we already checked exactly with the BoundVector
  if (lp_solver_->num_rows() == 0) {
    UpdateModelBounds();
    DLINEAR_DEBUG("DeltaLpTheorySolver::CheckSat: no rows, returning SAT");
    return TheoryResult::SAT;
  }

  // Set the bounds for the variables
  EnableVarBound();

  // Remove all the disabled rows from the LP solver
  DisableNotEnabledRows();

  // Now we call the solver
  DLINEAR_DEBUG_FMT("DeltaLpTheorySolver::CheckSat: calling SoPlex (phase {})", config_.simplex_sat_phase());

  const LpResult result = lp_solver_->Optimise(*actual_precision);

  switch (result) {
    case LpResult::OPTIMAL:
    case LpResult::UNBOUNDED:
    case LpResult::DELTA_OPTIMAL:
      UpdateModelSolution();
      DLINEAR_DEBUG("DeltaLpTheorySolver::CheckSat: returning DELTA_SAT");
      return TheoryResult::DELTA_SAT;
    case LpResult::INFEASIBLE:
      NotifyInfeasible(conflict_cb);
      DLINEAR_DEBUG("DeltaLpTheorySolver::CheckSat: returning UNSAT");
      return TheoryResult::UNSAT;
    case LpResult::ERROR:
      DLINEAR_ERROR("DeltaLpTheorySolver::CheckSat: returning ERROR");
      return TheoryResult::ERROR;
    default:
      DLINEAR_UNREACHABLE();
  }
}

}  // namespace dlinear