/**
 * @file DeltaSoplexTheorySolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "DeltaSoplexTheorySolver.h"

#include <map>
#include <utility>

#include "dlinear/libs/soplex.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

using SoplexStatus = soplex::SPxSolver::Status;
using soplex::Rational;

DeltaSoplexTheorySolver::DeltaSoplexTheorySolver(PredicateAbstractor &predicate_abstractor, const Config &config)
    : SoplexTheorySolver(predicate_abstractor, config) {}

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

  // Just create simple bound in LP
  // It will be handled when enabling the literal
  if (IsSimpleBound(formula)) return;

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
    DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
  }

  const int spx_row{spx_.numRowsRational()};

  // Add an inactive constraint with the right coefficients for the decisional variables
  soplex::DSVectorRational coeffs{ParseRowCoeff(formula)};
  spx_.addRowRational(soplex::LPRowRational(-soplex::infinity, coeffs, soplex::infinity));
  if (2 == simplex_sat_phase_) CreateArtificials(spx_row);

  // Update indexes
  lit_to_theory_row_.emplace(formulaVar.get_id(), spx_row);
  theory_row_to_lit_.emplace_back(formulaVar);
  theory_row_to_truth_.push_back(truth);

  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == theory_row_to_lit_.size() - 1, "incorrect theory_row_to_lit_.size()");
  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == spx_sense_.size() - 1, "incorrect spx_sense_.size()");
  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == spx_rhs_.size() - 1, "incorrect spx_rhs_.size()");
  DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::AddLinearLiteral({}{} ↦ {})", truth ? "" : "¬", it->second, spx_row);
}

std::optional<LiteralSet> DeltaSoplexTheorySolver::EnableLiteral(const Literal &lit) {
  Consolidate();
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");

  const auto &[var, truth] = lit;
  const auto it_row = lit_to_theory_row_.find(var.get_id());
  if (it_row != lit_to_theory_row_.end()) {
    // A non-trivial linear literal from the input problem
    const int spx_row = it_row->second;

    const LpRowSense sense = spx_sense_[spx_row];
    const mpq_class &rhs{spx_rhs_[spx_row]};
    if (truth) {
      if (sense == LpRowSense::NQ) return {};
      spx_.changeRangeRational(spx_row,
                               sense == LpRowSense::GE || sense == LpRowSense::EQ ? Rational(gmp::to_mpq_t(rhs))
                                                                                  : Rational(-soplex::infinity),
                               sense == LpRowSense::LE || sense == LpRowSense::EQ ? Rational(gmp::to_mpq_t(rhs))
                                                                                  : Rational(soplex::infinity));
    } else {
      if (sense == LpRowSense::EQ) return {};
      spx_.changeRangeRational(spx_row,
                               sense == LpRowSense::LE || sense == LpRowSense::NQ ? Rational(gmp::to_mpq_t(rhs))
                                                                                  : Rational(-soplex::infinity),
                               sense == LpRowSense::GE || sense == LpRowSense::NQ ? Rational(gmp::to_mpq_t(rhs))
                                                                                  : Rational(soplex::infinity));
    }
    // Update the truth value for the current iteration with the last SAT solver assignment
    theory_row_to_truth_[spx_row] = truth;
    DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::EnableLinearLiteral({}{})", truth ? "" : "¬", spx_row);
    return {};
  }

  // If the literal was not already among the constraints (rows) of the LP, it must be a bound
  // on a variable (column) or a learned literal.
  const auto it = predicate_abstractor_.var_to_formula_map().find(var);
  // The variable is not in the map (it is not a theory literal) or it is not a simple bound
  if (it == predicate_abstractor_.var_to_formula_map().end() || !IsSimpleBound(it->second)) {
    DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::EnableLinearLiteral: ignoring ({}, {})", var, truth);
    return {};
  }

  // A simple bound - set it directly
  DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::EnableLinearLiteral({}{})", truth ? "" : "¬", it->second);
  // bound = (variable, type, value), where:
  // - variable is the box variable
  // - type of bound
  // - value is the bound value
  Bound bound = GetBound(it->second, truth);
  // Since delta > 0, we can relax the bound type
  std::get<1>(bound) = ~std::get<1>(bound);
  // If the bound is now free, there is no need to consider it
  if (std::get<1>(bound) == LpColBound::F) return {};

  // Add the active bound to the LP solver bounds
  int theory_col = var_to_theory_col_[std::get<0>(bound).get_id()];
  bool valid_bound = SetSPXVarBound(bound, theory_col);
  theory_bound_to_explanation_[theory_col].insert(lit);
  // If the bound is invalid, return the explanation and update the SAT solver immediately
  if (!valid_bound) return theory_bound_to_explanation_[theory_col];
  return {};
}

bool DeltaSoplexTheorySolver::SetSPXVarBound(const Bound &bound, int spx_col) {
  const auto &[var, type, value] = bound;
  DLINEAR_ASSERT_FMT(type == LpColBound::L || type == LpColBound::U || type == LpColBound::B,
                     "type must be 'L', 'U', or 'B', received {}", type);

  if (value <= -soplex::infinity || value >= soplex::infinity) {
    DLINEAR_RUNTIME_ERROR_FMT("Simple bound too large: {}", value);
  }

  if (type == LpColBound::L || type == LpColBound::B) {
    if (gmp::to_mpq_t(value) > spx_lower_[spx_col]) {
      spx_lower_[spx_col] = gmp::to_mpq_t(value);
      DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::SetSPXVarBound ('{}'): set lower bound of {} to {}", type, var,
                        spx_lower_[spx_col]);
    }
  }
  if (type == LpColBound::U || type == LpColBound::B) {
    if (gmp::to_mpq_t(value) < spx_upper_[spx_col]) {
      spx_upper_[spx_col] = gmp::to_mpq_t(value);
      DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::SetSPXVarBound ('{}'): set upper bound of {} to {}", type, var,
                        spx_upper_[spx_col]);
    }
  }
  // Make sure there are no inverted bounds
  if (spx_lower_[spx_col] > spx_upper_[spx_col]) {
    DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::SetSPXVarBound: variable {} has invalid bounds [{}, {}]", var,
                      spx_lower_[spx_col], spx_upper_[spx_col]);
    return false;
  }
  return true;
}

SatResult DeltaSoplexTheorySolver::CheckSat(const Box &box, mpq_class *actual_precision, LiteralSet &explanation) {
  Consolidate();
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");

  static IterationStats stat{DLINEAR_INFO_ENABLED, "DeltaSoplexTheorySolver", "Total # of CheckSat",
                             "Total time spent in CheckSat"};
  TimerGuard check_sat_timer_guard(&stat.m_timer(), stat.enabled(), true /* start_timer */);
  stat.Increase();

  DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::CheckSat: Box = \n{}", box);

  SoplexStatus status = SoplexStatus::UNKNOWN;
  SatResult sat_status = SatResult::SAT_NO_RESULT;

  int rowcount = spx_.numRowsRational();
  int colcount = spx_.numColsRational();

  model_ = box;
  for (const Variable &var : theory_col_to_var_) {
    if (!model_.has_variable(var)) {
      // Variable should already be present
      DLINEAR_WARN_FMT("DeltaSoplexTheorySolver::CheckSat: Adding var {} to model from theory solver", var);
      model_.Add(var);
    }
  }

  // If we can immediately return SAT afterward
  if (rowcount == 0) {
    DLINEAR_DEBUG("DeltaSoplexTheorySolver::CheckSat: no need to call LP solver");
    UpdateModelBounds();
    return SatResult::SAT_DELTA_SATISFIABLE;
  }

  spx_.changeLowerRational(spx_lower_);
  spx_.changeUpperRational(spx_upper_);

  // Now we call the solver
  DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::CheckSat: calling SoPlex (phase {})",
                    1 == simplex_sat_phase_ ? "one" : "two");

  Rational max_violation, sum_violation;

  status = spx_.optimize();

  // If the simplex_sat_status is 2, we expect the status to be OPTIMAL
  // Otherwise, the status must be OPTIMAL, UNBOUNDED, or INFEASIBLE
  // Anything else is an error
  if ((2 == simplex_sat_phase_ && status != SoplexStatus::OPTIMAL) ||
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
  bool haveSoln = spx_.getPrimalRational(x);
  if (haveSoln && x.dim() != colcount) {
    DLINEAR_ASSERT(x.dim() >= colcount, "x.dim() must be >= colcount");
    DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::CheckSat: colcount = {} but x.dim() = {} after getPrimalRational()",
                      colcount, x.dim());
  }
  DLINEAR_ASSERT(status != SoplexStatus::OPTIMAL || haveSoln,
                 "status must either be not OPTIMAL or a solution must be present");

  if (1 == simplex_sat_phase_) {
    switch (status) {
      case SoplexStatus::OPTIMAL:
      case SoplexStatus::UNBOUNDED:
        sat_status = SatResult::SAT_DELTA_SATISFIABLE;
        break;
      case SoplexStatus::INFEASIBLE:
        sat_status = SatResult::SAT_UNSATISFIABLE;
        UpdateExplanation(explanation);
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
      if (haveSoln) {
        // Copy delta-feasible point from x into model_
        for (int theory_col = 0; theory_col < static_cast<int>(theory_col_to_var_.size()); theory_col++) {
          const Variable &var{theory_col_to_var_[theory_col]};
          DLINEAR_ASSERT(model_[var].lb() <= gmp::to_mpq_class(x[theory_col].backend().data()) &&
                             gmp::to_mpq_class(x[theory_col].backend().data()) <= model_[var].ub(),
                         "val must be in bounds");
          model_[var] = x[theory_col].backend().data();
        }
      } else {
        DLINEAR_RUNTIME_ERROR("delta-sat but no solution available: UNBOUNDED");
      }
      break;
    default:
      break;
  }
  DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::CheckSat: returning {}", sat_status);

  return sat_status;
}

}  // namespace dlinear
