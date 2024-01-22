//
// Created by c3054737 on 12/01/24.
//
#include "SoplexTheorySolver.h"

#include <utility>

#include "dlinear/util/Timer.h"
#include "dlinear/util/logging.h"

namespace dlinear {

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
  theory_bound_to_explanation_.emplace_back();
  DLINEAR_DEBUG_FMT("SoplexSatSolver::AddVariable({} ↦ {})", var, spx_col);
}

bool SoplexTheorySolver::SetSPXVarBound(const Bound &bound, int spx_col) {
  const auto &[var, type, value] = bound;
  DLINEAR_ASSERT_FMT(type == LpColBound::L || type == LpColBound::U || type == LpColBound::B || type == LpColBound::F,
                     "type must be 'L', 'U', 'B' or 'N', received {}", type);

  if (value <= -soplex::infinity || value >= soplex::infinity) {
    DLINEAR_RUNTIME_ERROR_FMT("Simple bound too large: {}", value);
  }

  if (type == LpColBound::L || type == LpColBound::B) {
    if (gmp::to_mpq_t(value) > spx_lower_[spx_col]) {
      spx_lower_[spx_col] = gmp::to_mpq_t(value);
      DLINEAR_TRACE_FMT("SoplexSatSolver::SetSPXVarBound ('{}'): set lower bound of {} to {}", type, var,
                        spx_lower_[spx_col]);
    }
  }
  if (type == LpColBound::U || type == LpColBound::B) {
    if (gmp::to_mpq_t(value) < spx_upper_[spx_col]) {
      spx_upper_[spx_col] = gmp::to_mpq_t(value);
      DLINEAR_TRACE_FMT("SoplexSatSolver::SetSPXVarBound ('{}'): set upper bound of {} to {}", type, var,
                        spx_upper_[spx_col]);
    }
  }
  // Make sure there are no inverted bounds
  if (spx_lower_[spx_col] > spx_upper_[spx_col]) {
    DLINEAR_DEBUG_FMT("SoplexSatSolver::SetSPXVarBound: variable {} has invalid bounds [{}, {}]", var,
                      spx_lower_[spx_col], spx_upper_[spx_col]);
    return false;
  }
  return true;
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

void SoplexTheorySolver::Reset(const Box &box) {
  DLINEAR_TRACE_FMT("SoplexSatSolver::Reset(): Box =\n{}", box);
  // Omitting to do this seems to cause problems in soplex
  spx_.clearBasis();
  // Clear all the sets in the bounds to explanation map
  for (auto &explanation : theory_bound_to_explanation_) explanation.clear();

  // Clear constraint bounds
  const int spx_rows = spx_.numRowsRational();
  DLINEAR_ASSERT(static_cast<size_t>(spx_rows) == theory_row_to_lit_.size(),
                 "spx_rows must be == from_spx_row_.size()");
  for (int i = 0; i < spx_rows; i++) spx_.changeRangeRational(i, -soplex::infinity, soplex::infinity);

  // Clear variable bounds
  [[maybe_unused]] const int spx_cols{spx_.numColsRational()};
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

void SoplexTheorySolver::UpdateModelBounds() {
  DLINEAR_ASSERT(spx_.numRowsRational() == 0, "There must be no rows in the LP solver");
  DLINEAR_ASSERT(std::all_of(theory_col_to_var_.cbegin(), theory_col_to_var_.cend(),
                             [this](const std::pair<int, Variable> &it) {
                               const auto &[theory_col, var] = it;
                               return spx_lower_[theory_col] <= spx_upper_[theory_col];
                             }),
                 "All lower bounds must be <= upper bounds");

  // Update the box with the new bounds, since the theory solver won't be called, for there are no constraints.
  for (const auto &[theory_col, var] : theory_col_to_var_) {
    const Rational &lb{spx_lower_[theory_col]};
    const Rational &ub{spx_upper_[theory_col]};
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
void SoplexTheorySolver::UpdateExplanation(LiteralSet &explanation) {
  const int rowcount = spx_.numRowsRational();
  soplex::VectorRational ray;
  ray.reDim(rowcount);
  // Get the Farkas ray to identify which rows are responsible for the conflict
  [[maybe_unused]] bool res = spx_.getDualFarkasRational(ray);
  DLINEAR_ASSERT(res, "getDualFarkasRational() must return true");
  explanation.clear();
  // For each row in the ray
  for (int i = 0; i < rowcount; ++i) {
    if (ray[i] == 0) continue;  // The row did not participate in the conflict, ignore it
    DLINEAR_TRACE_FMT("SoplexSatSolver::UpdateExplanation: ray[{}] = {}", i, ray[i]);
    const Literal &lit = theory_row_to_lit_[i];
    // Insert the conflicting row literal to the explanation. Use the latest truth value from the SAT solver
    explanation.insert({lit.first, theory_row_to_truth_[i]});
    // For each free variable in the literal, add their bounds to the explanation
    for (const auto &col_var : predicate_abstractor_[lit.first].GetFreeVariables()) {
      int theory_col = var_to_theory_col_.at(col_var.get_id());
      const LiteralSet &theory_bound_to_explanation = theory_bound_to_explanation_.at(theory_col);
      explanation.insert(theory_bound_to_explanation.cbegin(), theory_bound_to_explanation.cend());
    }
  }
}

}  // namespace dlinear
