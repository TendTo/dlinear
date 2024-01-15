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

namespace {
class SoplexTheorySolverStats : public Stats {
 public:
  explicit SoplexTheorySolverStats(const bool enabled) : Stats{enabled} {}
  SoplexTheorySolverStats(const SoplexTheorySolverStats &) = delete;
  SoplexTheorySolverStats(SoplexTheorySolverStats &&) = delete;
  SoplexTheorySolverStats &operator=(const SoplexTheorySolverStats &) = delete;
  SoplexTheorySolverStats &operator=(SoplexTheorySolverStats &&) = delete;
  ~SoplexTheorySolverStats() override {
    if (enabled()) std::cout << ToString() << std::endl;
  }
  std::string ToString() const override {
    return fmt::format(DLINEAR_STATS_FMT, "Total # of CheckSat", "Theory level", num_check_sat_,
                       "Total time spent in CheckSat", "Theory level", timer_check_sat_.seconds());
  }
  void increase_num_check_sat() { increase(&num_check_sat_); }

  Timer timer_check_sat_;

 private:
  std::atomic<int> num_check_sat_{0};
};
}  // namespace

SoplexTheorySolver::SoplexTheorySolver(PredicateAbstractor &predicate_abstractor, const Config &config)
    : TheorySolver(predicate_abstractor, config) {
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
  if (it != var_to_theory_col_.end()) {
    // Found.
    return;
  }
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

void SoplexTheorySolver::AddLiteral(const Literal &lit) {
  const auto &[formulaVar, truth] = lit;
  const auto &var_to_formula_map = predicate_abstractor_.var_to_formula_map();
  const auto it = var_to_formula_map.find(formulaVar);
  // Boolean variable - no need to involve theory solver
  if (it == var_to_formula_map.end()) return;
  const auto it2 = lit_to_theory_row_.find({formulaVar.get_id(), truth});
  // Literal is already present
  if (it2 != lit_to_theory_row_.end()) return;

  // Theory formula
  const Formula &formula = it->second;
  // Create the LP solver variables
  for (const Variable &var : formula.GetFreeVariables()) AddVariable(var);

  if (IsEqualToOrWhatever(formula, truth)) {
    if (IsSimpleBound(formula)) {
      return;  // Just create simple bound in LP
    }
    spx_sense_.push_back('E');
  } else if (IsGreaterThanOrWhatever(formula, truth)) {
    if (IsSimpleBound(formula)) {
      return;
    }
    spx_sense_.push_back('G');
  } else if (IsLessThanOrWhatever(formula, truth)) {
    if (IsSimpleBound(formula)) {
      return;
    }
    spx_sense_.push_back('L');
  } else if (IsNotEqualToOrWhatever(formula, truth)) {
    // Nothing to do, because this constraint is always delta-sat for
    // delta > 0.
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
  lit_to_theory_row_.emplace(std::make_pair(formulaVar.get_id(), truth), spx_row);
  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == theory_row_to_lit_.size(), "spx_row must match from_spx_row_.size()");
  theory_row_to_lit_.emplace_back(formulaVar, truth);
  DLINEAR_DEBUG_FMT("SoplexSatSolver::AddLinearLiteral({}{} ↦ {})", truth ? "" : "¬", it->second, spx_row);
}

void SoplexTheorySolver::EnableLiteral(const Literal &lit) {
  const Variable &var = lit.first;
  const bool truth = lit.second;

  const auto it_row = lit_to_theory_row_.find({var.get_id(), truth});
  if (it_row != lit_to_theory_row_.end()) {
    // A non-trivial linear literal from the input problem
    const int spx_row = it_row->second;
    const char sense{spx_sense_[spx_row]};
    const mpq_class &rhs{spx_rhs_[spx_row]};
    spx_.changeRangeRational(spx_row,
                             sense == 'G' || sense == 'E' ? Rational(gmp::to_mpq_t(rhs)) : Rational(-soplex::infinity),
                             sense == 'L' || sense == 'E' ? Rational(gmp::to_mpq_t(rhs)) : Rational(soplex::infinity));
    DLINEAR_TRACE_FMT("SoplexSatSolver::EnableLinearLiteral({})", spx_row);
    return;
  }

  // If the literal was not already among the constraints (rows) of the LP, it must be a bound
  // on a variable (column), a learned literal, or a not-equal literal from the
  // input problem (if delta > 0).
  const auto it = predicate_abstractor_.var_to_formula_map().find(var);
  // The variable is not in the map (it is not a theory literal) or it is not a simple bound
  if (it == predicate_abstractor_.var_to_formula_map().end() || !IsSimpleBound(it->second)) {
    DLINEAR_TRACE_FMT("SoplexSatSolver::EnableLinearLiteral: ignoring ({}, {})", var, truth);
    return;
  }

  // A simple bound - set it directly
  const Formula &formula{it->second};
  const Expression &lhs{get_lhs_expression(formula)};
  const Expression &rhs{get_rhs_expression(formula)};
  DLINEAR_TRACE_FMT("SoplexSatSolver::EnableLinearLiteral({}{})", truth ? "" : "¬", formula);
  if (IsEqualToOrWhatever(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) {
      SetSPXVarBound(get_variable(lhs), 'B', get_constant_value(rhs));
    } else if (is_constant(lhs) && is_variable(rhs)) {
      SetSPXVarBound(get_variable(rhs), 'B', get_constant_value(lhs));
    } else {
      DLINEAR_UNREACHABLE();
    }
  } else if (IsGreaterThanOrWhatever(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) {
      SetSPXVarBound(get_variable(lhs), 'L', get_constant_value(rhs));
    } else if (is_constant(lhs) && is_variable(rhs)) {
      SetSPXVarBound(get_variable(rhs), 'U', get_constant_value(lhs));
    } else {
      DLINEAR_UNREACHABLE();
    }
  } else if (IsLessThanOrWhatever(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) {
      SetSPXVarBound(get_variable(lhs), 'U', get_constant_value(rhs));
    } else if (is_constant(lhs) && is_variable(rhs)) {
      SetSPXVarBound(get_variable(rhs), 'L', get_constant_value(lhs));
    } else {
      DLINEAR_UNREACHABLE();
    }
  } else if (IsNotEqualToOrWhatever(formula, truth)) {
    // If delta > 0, we can ignore not-equal bounds on variables, for they will always be satisfied.
    // TODO: This should be addressed in case of delta == 0.
    // Since Soplex is not able to handle inverted bounds, not equal should be handled by adding a new row
    // to the LP.
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
  }
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
  static SoplexTheorySolverStats stat{DLINEAR_INFO_ENABLED};
  stat.increase_num_check_sat();
  TimerGuard check_sat_timer_guard(&stat.timer_check_sat_, stat.enabled(), true /* start_timer */);

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
        sat_status = *actual_precision == 0.0 ? SatResult::SAT_SATISFIABLE : SatResult::SAT_DELTA_SATISFIABLE;
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
      sat_status = *actual_precision == 0.0 ? SatResult::SAT_SATISFIABLE : SatResult::SAT_DELTA_SATISFIABLE;
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