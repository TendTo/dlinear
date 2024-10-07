/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "DeltaSoplexTheorySolver.h"

#include <algorithm>
#include <cstddef>
#include <map>

#include "dlinear/libs/libsoplex.h"
#include "dlinear/solver/LpRowSense.h"
#include "dlinear/symbolic/symbolic.h"
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
  DLINEAR_ASSERT(!is_consolidated_, "Cannot add literals after consolidation");
  // Literal is already present
  if (lit_to_theory_row_.contains(formula_var.get_id())) return;

  DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::AddLiteral({})", formula);

  // Create the LP solver variables
  for (const Variable &var : formula.GetFreeVariables()) AddVariable(var);
  if (BoundPreprocessor::IsSimpleBound(formula)) return;

  const int spx_row{spx_rows_.num()};
  soplex::DSVectorRational coeffs{ParseRowCoeff(formula)};
  spx_rows_.add(soplex::LPRowRational(-soplex::infinity, coeffs, soplex::infinity));
  spx_sense_.emplace_back(~parseLpSense(formula));

  // Update indexes
  lit_to_theory_row_.emplace(formula_var.get_id(), spx_row);
  theory_row_to_lit_.emplace_back(formula_var, true);

  DLINEAR_ASSERT(static_cast<std::size_t>(spx_row) == theory_row_to_lit_.size() - 1,
                 "incorrect theory_row_to_lit_.size()");
  DLINEAR_ASSERT(static_cast<std::size_t>(spx_row) == spx_sense_.size() - 1, "incorrect spx_sense_.size()");
  DLINEAR_ASSERT(static_cast<std::size_t>(spx_row) == spx_rhs_.size() - 1, "incorrect spx_rhs_.size()");
  DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::AddLiteral: {} ↦ {}", formula, spx_row);
}

DeltaSoplexTheorySolver::Explanations DeltaSoplexTheorySolver::EnableLiteral(const Literal &lit) {
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");
  DLINEAR_ASSERT(predicate_abstractor_.var_to_formula_map().contains(lit.var), "var must map to a theory literal");

  Explanations explanations{preprocessor_.EnableLiteral(lit)};
  if (!explanations.empty()) return explanations;

  const auto &[var, truth] = lit;
  const auto it = lit_to_theory_row_.find(var.get_id());
  // If the literal was not already among the constraints (rows) of the LP, it must be a learned literal.
  if (it == lit_to_theory_row_.end()) {
    DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::EnableLinearLiteral: ignoring ({})", lit);
    return {};
  }

  // A non-trivial linear literal from the input problem
  const int spx_row = it->second;
  // Update the truth value for the current iteration with the last SAT solver assignment
  theory_row_to_lit_[spx_row].truth = truth;

  DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::EnableLinearLiteral({})", lit);

  EnableSpxRow(spx_row, truth);
  return explanations;
}

SatResult DeltaSoplexTheorySolver::CheckSatCore(mpq_class *actual_precision, Explanations &explanations) {
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before checking for sat");

  // Set the bounds for the variables
  EnableSpxVarBound();
  // Remove all the disabled rows from the LP solver
  DisableSpxRows();

  // Now we call the solver
  DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::CheckSat: calling SoPlex (phase {})", config_.simplex_sat_phase());
  Rational max_violation, sum_violation;
  SoplexStatus status = spx_.optimize();

  // The status must be OPTIMAL, UNBOUNDED, or INFEASIBLE. Anything else is an error
  if (status != SoplexStatus::OPTIMAL && status != SoplexStatus::UNBOUNDED && status != SoplexStatus::INFEASIBLE) {
    DLINEAR_RUNTIME_ERROR_FMT("SoPlex returned {}. That's not allowed here", status);
  } else if (spx_.getRowViolationRational(max_violation, sum_violation)) {
    *actual_precision = gmp::to_mpq_class(max_violation.backend().data());
    DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::CheckSat: SoPlex returned {}, precision = {}", status,
                      *actual_precision);
  } else {
    DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::CheckSat: SoPlex has returned {}, but no precision", status);
  }

  switch (status) {
    case SoplexStatus::OPTIMAL:
      UpdateModelSolution();
      DLINEAR_DEBUG("DeltaSoplexTheorySolver::CheckSat: returning SAT_DELTA_SATISFIABLE");
      return SatResult::SAT_DELTA_SATISFIABLE;
    case SoplexStatus::INFEASIBLE:
      UpdateExplanations(explanations);
      DLINEAR_DEBUG("DeltaSoplexTheorySolver::CheckSat: returning SAT_UNSATISFIABLE");
      return SatResult::SAT_UNSATISFIABLE;
    default:
      DLINEAR_UNREACHABLE();
  }
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
