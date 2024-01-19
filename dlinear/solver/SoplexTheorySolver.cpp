//
// Created by c3054737 on 12/01/24.
//
#include "SoplexTheorySolver.h"

#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/logging.h"

namespace dlinear {

using SoplexStatus = soplex::SPxSolver::Status;
using soplex::Rational;

Rational SoplexTheorySolver::infinity_{0};
Rational SoplexTheorySolver::ninfinity_{0};

SoplexTheorySolver::SoplexTheorySolver(PredicateAbstractor &predicate_abstractor, const Config &config)
    : TheorySolver(predicate_abstractor, config) {
  // Initialize infinities
  infinity_ = soplex::infinity;
  ninfinity_ = -soplex::infinity;
  // Default SoPlex parameters
  spx_.setRealParam(soplex::SoPlex::FEASTOL, config.precision());
  spx_.setBoolParam(soplex::SoPlex::RATREC, false);
  spx_.setIntParam(soplex::SoPlex::READMODE, soplex::SoPlex::READMODE_RATIONAL);
  spx_.setIntParam(soplex::SoPlex::SOLVEMODE, soplex::SoPlex::SOLVEMODE_RATIONAL);
  spx_.setIntParam(soplex::SoPlex::CHECKMODE, soplex::SoPlex::CHECKMODE_RATIONAL);
  spx_.setIntParam(soplex::SoPlex::SYNCMODE, soplex::SoPlex::SYNCMODE_AUTO);
  spx_.setIntParam(soplex::SoPlex::VERBOSITY, config.verbose_simplex());
  // Default is maximize.
  spx_.setIntParam(soplex::SoPlex::OBJSENSE, soplex::SoPlex::OBJSENSE_MINIMIZE);
  // Enable precision boosting
  bool enable_precision_boosting = config.lp_mode() != Config::LPMode::PURE_ITERATIVE_REFINEMENT;
  spx_.setBoolParam(soplex::SoPlex::ADAPT_TOLS_TO_MULTIPRECISION, enable_precision_boosting);
  spx_.setBoolParam(soplex::SoPlex::PRECISION_BOOSTING, enable_precision_boosting);
  spx_.setIntParam(soplex::SoPlex::RATFAC_MINSTALLS, enable_precision_boosting ? 0 : 2);
  // Enable iterative refinement
  bool enable_iterative_refinement = config.lp_mode() != Config::LPMode::PURE_PRECISION_BOOSTING;
  spx_.setBoolParam(soplex::SoPlex::ITERATIVE_REFINEMENT, enable_iterative_refinement);
  DLINEAR_DEBUG_FMT(
      "SoplexTheorySolver::SoplexTheorySolver: precision = {}, precision_boosting = {}, iterative_refinement = {}",
      config.precision(), enable_precision_boosting, enable_iterative_refinement);
}

void SoplexTheorySolver::AddVariable(const Variable &var) {
  auto it = var_to_theory_col_.find(var.get_id());
  // The variable is already present
  if (it != var_to_theory_col_.end()) return;

  const int spx_col{spx_.numColsRational()};
  spx_lower_.reDim(spx_col + 1, false);
  spx_upper_.reDim(spx_col + 1, false);
  spx_lower_[spx_col] = -soplex::infinity;  // Set unbounded
  spx_upper_[spx_col] = soplex::infinity;
  // obj, coeffs, upper, lower
  spx_.addColRational(soplex::LPColRational(0, soplex::DSVectorRational(), soplex::infinity, -soplex::infinity));
  var_to_theory_col_.emplace(var.get_id(), spx_col);
  theory_col_to_var_[spx_col] = var;
  DLINEAR_DEBUG_FMT("SoplexSatSolver::AddVariable({} ↦ {})", var, spx_col);
}

void SoplexTheorySolver::SetSPXVarBound(const Variable &var, const char type, const mpq_class &value) {
  DLINEAR_ASSERT(type == 'L' || type == 'U' || type == 'B', "type must be 'L', 'U', or 'B'");
  const auto it = var_to_theory_col_.find(var.get_id());

  if (it == var_to_theory_col_.end()) DLINEAR_RUNTIME_ERROR_FMT("Variable undefined: {}", var);
  if (value <= -soplex::infinity || value >= soplex::infinity) {
    DLINEAR_RUNTIME_ERROR_FMT("Simple bound too large: {}", value);
  }

  if (type == 'L' || type == 'B') {
    if (gmp::to_mpq_t(value) > spx_lower_[it->second]) {
      spx_lower_[it->second] = gmp::to_mpq_t(value);
      DLINEAR_TRACE_FMT("SoplexSatSolver::SetSPXVarBound ('{}'): set lower bound of {} to {}", type, var,
                        spx_lower_[it->second]);
    }
  }
  if (type == 'U' || type == 'B') {
    if (gmp::to_mpq_t(value) < spx_upper_[it->second]) {
      spx_upper_[it->second] = gmp::to_mpq_t(value);
      DLINEAR_TRACE_FMT("SoplexSatSolver::SetSPXVarBound ('{}'): set upper bound of {} to {}", type, var,
                        spx_upper_[it->second]);
    }
  }
}

void SoplexTheorySolver::SetSPXVarCoeff(soplex::DSVectorRational &coeffs, const Variable &var, const mpq_class &value) {
  const auto it = var_to_theory_col_.find(var.get_id());
  if (it == var_to_theory_col_.end()) DLINEAR_RUNTIME_ERROR_FMT("Variable undefined: {}", var);
  if (value <= -soplex::infinity || value >= soplex::infinity) {
    DLINEAR_RUNTIME_ERROR_FMT("LP coefficient too large: {}", value);
  }
  coeffs.add(it->second, gmp::to_mpq_t(value));
}

void SoplexTheorySolver::CreateArtificials(const int spx_row) {
  DLINEAR_ASSERT(2 == simplex_sat_phase_, "must be phase 2");
  const int spx_cols{spx_.numColsRational()};
  spx_lower_.reDim(spx_cols + 2, true);  // Set lower bounds to zero
  spx_upper_.reDim(spx_cols + 2, false);
  spx_upper_[spx_cols] = soplex::infinity;  // Set upper bounds to infinity
  spx_upper_[spx_cols + 1] = soplex::infinity;
  soplex::DSVectorRational coeffsPos;
  coeffsPos.add(spx_row, 1);
  spx_.addColRational(soplex::LPColRational(1, coeffsPos, soplex::infinity, 0));
  soplex::DSVectorRational coeffsNeg;
  coeffsNeg.add(spx_row, -1);
  spx_.addColRational(soplex::LPColRational(1, coeffsNeg, soplex::infinity, 0));
  DLINEAR_DEBUG_FMT("SoplexSatSolver::CreateArtificials({} -> ({}, {}))", spx_row, spx_cols, spx_cols + 1);
}

SatResult SoplexTheorySolver::CheckSat(const Box &box, mpq_class *actual_precision) {
  static IterationStats stat{DLINEAR_INFO_ENABLED, "SoplexTheorySolver", "Total # of CheckSat",
                             "Total time spent in CheckSat"};
  TimerGuard check_sat_timer_guard(&stat.mutable_timer(), stat.enabled(), true /* start_timer */);
  stat.Increase();

  DLINEAR_TRACE_FMT("SoplexTheorySolver::CheckSat: Box = \n{}", box);

  SoplexStatus status = SoplexStatus::UNKNOWN;
  SatResult sat_status = SatResult::SAT_NO_RESULT;

  int rowcount = spx_.numRowsRational();
  int colcount = spx_.numColsRational();

  model_ = box;
  for (const std::pair<const int, Variable> &kv : theory_col_to_var_) {
    if (!model_.has_variable(kv.second)) {
      // Variable should already be present
      DLINEAR_WARN_FMT("SoplexTheorySolver::CheckSat: Adding var {} to model from theory solver", kv.second);
      model_.Add(kv.second);
    }
  }

  // The solver can't handle problems with inverted bounds, so we need to
  // handle that here.
  // Also, if there are no constraints, we can immediately return SAT afterward if the bounds are OK.
  for (const auto &[theory_col, var] : theory_col_to_var_) {
    const Rational &lb{spx_lower_[theory_col]};
    const Rational &ub{spx_upper_[theory_col]};
    if (lb > ub) {
      DLINEAR_DEBUG_FMT("SoplexTheorySolver::CheckSat: variable {} has invalid bounds [{}, {}]", var, lb, ub);
      return SatResult::SAT_UNSATISFIABLE;
    }
    if (rowcount == 0) {
      Rational val;
      if (-soplex::infinity < lb) {
        val = lb;
      } else if (ub < soplex::infinity) {
        val = ub;
      } else {
        val = 0;
      }
      DLINEAR_ASSERT(gmp::to_mpq_t(model_[var].lb()) <= val && val <= gmp::to_mpq_t(model_[var].ub()),
                     "val must be in bounds");
      model_[var] = val.backend().data();
    }
  }
  if (rowcount == 0) {
    DLINEAR_DEBUG("SoplexTheorySolver::CheckSat: no need to call LP solver");
    return SatResult::SAT_SATISFIABLE;
  }

  spx_.changeLowerRational(spx_lower_);
  spx_.changeUpperRational(spx_upper_);

  // Now we call the solver
  DLINEAR_DEBUG_FMT("SoplexTheorySolver::CheckSat: calling SoPlex (phase {})", 1 == simplex_sat_phase_ ? "one" : "two");

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
    DLINEAR_DEBUG_FMT("SoplexTheorySolver::CheckSat: SoPlex returned {}, precision = {}", status, *actual_precision);
  } else {
    DLINEAR_DEBUG_FMT("SoplexTheorySolver::CheckSat: SoPlex has returned {}, but no precision", status);
  }

  soplex::VectorRational x;
  x.reDim(colcount);
  bool haveSoln = spx_.getPrimalRational(x);
  if (haveSoln && x.dim() != colcount) {
    DLINEAR_ASSERT(x.dim() >= colcount, "x.dim() must be > colcount");
    DLINEAR_WARN_FMT("SoplexTheorySolver::CheckSat: colcount = {} but x.dim() = {} after getPrimalRational()", colcount,
                     x.dim());
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
    case SatResult::SAT_SATISFIABLE:
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
        DLINEAR_RUNTIME_ERROR("delta-sat but no solution available");
      }
      break;
    default:
      break;
  }
  DLINEAR_DEBUG_FMT("SoplexTheorySolver::CheckSat: returning {}", sat_status);

  return sat_status;
}

void SoplexTheorySolver::Reset(const Box &box) {
  DLINEAR_TRACE_FMT("SoplexSatSolver::Reset(): Box =\n{}", box);
  // Omitting to do this seems to cause problems in soplex
  spx_.clearBasis();

  // Clear constraint bounds
  const int spx_rows = spx_.numRowsRational();
  DLINEAR_ASSERT(static_cast<size_t>(spx_rows) == theory_row_to_lit_.size(),
                 "spx_rows must be == from_spx_row_.size()");
  for (int i = 0; i < spx_rows; i++) spx_.changeRangeRational(i, -soplex::infinity, soplex::infinity);

  // Clear variable bounds
  const int spx_cols{spx_.numColsRational()};
  DLINEAR_ASSERT(2 == simplex_sat_phase_ || static_cast<size_t>(spx_cols) == theory_col_to_var_.size(),
                 "spx_cols must match from_spx_col_.size(), unless we are in phase 2");
  for (const auto &[theory_col, var] : theory_col_to_var_) {
    DLINEAR_ASSERT(0 <= theory_col && theory_col < spx_cols, "theory_col must be in bounds");
    if (box.has_variable(var)) {
      DLINEAR_ASSERT(-soplex::infinity <= box[var].lb(), "lower bound must be >= -infinity");
      DLINEAR_ASSERT(box[var].lb() <= box[var].ub(), "lower bound must be <= upper bound");
      DLINEAR_ASSERT(box[var].ub() <= soplex::infinity, "upper bound must be <= infinity");
      spx_lower_[theory_col] = gmp::to_mpq_t(box[var].lb());
      spx_upper_[theory_col] = gmp::to_mpq_t(box[var].ub());
    } else {
      spx_lower_[theory_col] = -soplex::infinity;
      spx_upper_[theory_col] = soplex::infinity;
    }
    spx_.changeBoundsRational(theory_col, -soplex::infinity, soplex::infinity);
  }
}

}  // namespace dlinear