//
// Created by c3054737 on 17/01/24.
//

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

  if (IsEqualTo(formula, truth)) {
    // Just create simple bound in LP
    if (IsSimpleBound(formula)) return;
    spx_sense_.push_back('E');
  } else if (IsGreaterThan(formula, truth) || IsGreaterThanOrEqualTo(formula, truth)) {
    // Just create simple bound in LP
    if (IsSimpleBound(formula)) return;
    spx_sense_.push_back('G');
  } else if (IsLessThan(formula, truth) || IsLessThanOrEqualTo(formula, truth)) {
    // Just create simple bound in LP
    if (IsSimpleBound(formula)) return;
    spx_sense_.push_back('L');
  } else if (IsNotEqualTo(formula, truth)) {
    // Nothing to do, because this constraint is always delta-sat for delta > 0.
    return;
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
  }

  Expression expr{(get_lhs_expression(formula) - get_rhs_expression(formula)).Expand()};
  const int spx_row{spx_.numRowsRational()};
  soplex::DSVectorRational coeffs;
  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == spx_sense_.size() - 1, "spx_row must match spx_sense_.size() - 1");
  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == spx_rhs_.size(), "spx_row must match spx_rhs_.size()");
  spx_rhs_.emplace_back(0);
  if (is_constant(expr)) {
    spx_rhs_.back() = -get_constant_value(expr);
  } else if (is_variable(expr)) {
    SetSPXVarCoeff(coeffs, get_variable(expr), 1);
  } else if (is_multiplication(expr)) {
    std::map<Expression, Expression> map = get_base_to_exponent_map_in_multiplication(expr);
    if (map.size() != 1 || !is_variable(map.begin()->first) || !is_constant(map.begin()->second) ||
        get_constant_value(map.begin()->second) != 1) {
      DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", expr);
    }
    SetSPXVarCoeff(coeffs, get_variable(map.begin()->first), get_constant_in_multiplication(expr));
  } else if (is_addition(expr)) {
    const std::map<Expression, mpq_class> &map = get_expr_to_coeff_map_in_addition(expr);
    for (const auto &pair : map) {
      if (!is_variable(pair.first)) {
        DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", expr);
      }
      SetSPXVarCoeff(coeffs, get_variable(pair.first), pair.second);
    }
    spx_rhs_.back() = -get_constant_in_addition(expr);
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", expr);
  }
  if (spx_rhs_.back() <= -soplex::infinity || spx_rhs_.back() >= soplex::infinity) {
    DLINEAR_RUNTIME_ERROR_FMT("LP RHS value too large: {}", spx_rhs_.back());
  }

  // Add inactive constraint
  spx_.addRowRational(soplex::LPRowRational(-soplex::infinity, coeffs, soplex::infinity));
  if (2 == simplex_sat_phase_) CreateArtificials(spx_row);

  // Update indexes
  lit_to_theory_row_.emplace(formulaVar.get_id(), std::tuple(truth, spx_row, -1));
  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == theory_row_to_lit_.size(), "spx_row must match from_spx_row_.size()");
  theory_row_to_lit_.emplace_back(formulaVar, truth);
  DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::AddLinearLiteral({}{} ↦ {})", truth ? "" : "¬", it->second, spx_row);
}

std::optional<LiteralSet> DeltaSoplexTheorySolver::EnableLiteral(const Literal &lit) {
  const Variable &var = lit.first;
  const bool truth = lit.second;

  const auto it_row = lit_to_theory_row_.find(var.get_id());
  if (it_row != lit_to_theory_row_.end()) {
    // A non-trivial linear literal from the input problem
    const auto &[stored_truth, spx_row, spx_row2] = it_row->second;

    if (stored_truth == truth) {
      const char sense = spx_sense_[spx_row];
      const mpq_class &rhs{spx_rhs_[spx_row]};
      spx_.changeRangeRational(
          spx_row, sense == 'G' || sense == 'E' ? Rational(gmp::to_mpq_t(rhs)) : Rational(-soplex::infinity),
          sense == 'L' || sense == 'E' ? Rational(gmp::to_mpq_t(rhs)) : Rational(soplex::infinity));
      DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::EnableLinearLiteral({})", spx_row);
      return {};
    }
  }

  // If the literal was not already among the constraints (rows) of the LP, it must be a bound
  // on a variable (column), a learned literal, or a not-equal literal from the
  // input problem (if delta > 0).
  const auto it = predicate_abstractor_.var_to_formula_map().find(var);
  // The variable is not in the map (it is not a theory literal) or it is not a simple bound
  if (it == predicate_abstractor_.var_to_formula_map().end() || !IsSimpleBound(it->second)) {
    DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::EnableLinearLiteral: ignoring ({}, {})", var, truth);
    return {};
  }

  // A simple bound - set it directly
  DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::EnableLinearLiteral({}{})", truth ? "" : "¬", it->second);
  // bound = (variable, type, value)
  // variable is the box variable
  // type is 'L' for lower bound, 'U' for upper bound, 'B' for both, 'N' for not equal and 'I' for ignore
  // value is the bound value
  std::tuple<const Variable &, const char, const mpq_class &> bound = GetBound(it->second, truth);
  // If the bound type is 'I' or 'N', we can just ignore the bound
  if (std::get<1>(bound) == 'I' || std::get<1>(bound) == 'N') return {};

  // Add the active bound to the LP solver bounds
  int theory_col = var_to_theory_col_[std::get<0>(bound).get_id()];
  bool valid_bound = SetSPXVarBound(bound, theory_col);
  theory_col_to_explanation_[theory_col].insert(lit);
  // If the bound is invalid, return the explanation and update the SAT solver immediately
  if (!valid_bound) return theory_col_to_explanation_[theory_col];
  return {};
}

SatResult DeltaSoplexTheorySolver::CheckSat(const Box &box, mpq_class *actual_precision, LiteralSet &explanation) {
  static IterationStats stat{DLINEAR_INFO_ENABLED, "DeltaSoplexTheorySolver", "Total # of CheckSat",
                             "Total time spent in CheckSat"};
  TimerGuard check_sat_timer_guard(&stat.mutable_timer(), stat.enabled(), true /* start_timer */);
  stat.Increase();

  DLINEAR_TRACE_FMT("DeltaSoplexTheorySolver::CheckSat: Box = \n{}", box);

  SoplexStatus status = SoplexStatus::UNKNOWN;
  SatResult sat_status = SatResult::SAT_NO_RESULT;

  int rowcount = spx_.numRowsRational();
  int colcount = spx_.numColsRational();

  model_ = box;
  for (const std::pair<const int, Variable> &kv : theory_col_to_var_) {
    if (!model_.has_variable(kv.second)) {
      // Variable should already be present
      DLINEAR_WARN_FMT("DeltaSoplexTheorySolver::CheckSat: Adding var {} to model from theory solver", kv.second);
      model_.Add(kv.second);
    }
  }

  // The solver can't handle problems with inverted bounds, so we need to handle that here
  if (!CheckBounds()) return SatResult::SAT_UNSATISFIABLE;

  // If we can immediately return SAT afterward
  if (rowcount == 0) {
    DLINEAR_DEBUG("DeltaSoplexTheorySolver::CheckSat: no need to call LP solver");
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
    DLINEAR_ASSERT(x.dim() >= colcount, "x.dim() must be > colcount");
    DLINEAR_WARN_FMT("DeltaSoplexTheorySolver::CheckSat: colcount = {} but x.dim() = {} after getPrimalRational()",
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
        {
          soplex::VectorRational infeasibility_rows;
          infeasibility_rows.reDim(rowcount);
          [[maybe_unused]] bool res = spx_.getDualFarkasRational(infeasibility_rows);
          DLINEAR_ASSERT(res, "getDualFarkasRational() must return true");
          explanation.clear();
          for (int i = 0; i < rowcount; ++i) {
            if (infeasibility_rows[i] > 0) explanation.insert(theory_row_to_lit_[i]);
          }
        }
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
        for (const auto &[theory_col, var] : theory_col_to_var_) {
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
