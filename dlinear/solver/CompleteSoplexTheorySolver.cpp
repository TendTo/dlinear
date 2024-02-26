/**
 * @file CompleteSoplexTheorySolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "CompleteSoplexTheorySolver.h"

#include <map>
#include <utility>

#include "dlinear/libs/soplex.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/BitIncrementIterator.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

using SoplexStatus = soplex::SPxSolver::Status;
using soplex::Rational;

CompleteSoplexTheorySolver::CompleteSoplexTheorySolver(PredicateAbstractor &predicate_abstractor, const Config &config)
    : SoplexTheorySolver(predicate_abstractor, config) {}

void CompleteSoplexTheorySolver::AddVariable(const Variable &var) {
  auto it = var_to_theory_col_.find(var.get_id());
  // The variable is already present
  if (it != var_to_theory_col_.end()) return;
  SoplexTheorySolver::AddVariable(var);
  // Add the set of differences for the new variable that will map to a column of the LP problem
  spx_nq_.emplace_back();
  var_to_enabled_theory_rows_.emplace(var.get_id(), std::vector<int>());
}

void CompleteSoplexTheorySolver::AddLiteral(const Literal &lit) {
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
  } else if (IsGreaterThan(formula)) {
    spx_sense_.push_back(LpRowSense::GT);
  } else if (IsGreaterThanOrEqualTo(formula)) {
    spx_sense_.push_back(LpRowSense::GE);
  } else if (IsLessThan(formula)) {
    spx_sense_.push_back(LpRowSense::LT);
  } else if (IsLessThanOrEqualTo(formula)) {
    spx_sense_.push_back(LpRowSense::LE);
  } else if (IsNotEqualTo(formula)) {
    spx_sense_.push_back(LpRowSense::NQ);
  } else {
    DLINEAR_UNREACHABLE();
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
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::AddLinearLiteral({}{} ↦ {})", truth ? "" : "¬", it->second, spx_row);
}

std::optional<LiteralSet> CompleteSoplexTheorySolver::EnableLiteral(const Literal &lit) {
  Consolidate();
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");

  const auto &[var, truth] = lit;
  const auto it_row = lit_to_theory_row_.find(var.get_id());

  // If the literal was not already among the constraints (rows) of the LP, it must be a learned literal.
  if (it_row == lit_to_theory_row_.end()) {
    DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::EnableLinearLiteral: ignoring ({}, {})", var, truth);
    return {};
  }

  // A non-trivial linear literal from the input problem
  const int spx_row = it_row->second;

  // A simple bound - set it directly
  DLINEAR_ASSERT(predicate_abstractor_.var_to_formula_map().count(var) != 0, "var maps to a theory literal");
  const Formula &formula = predicate_abstractor_.var_to_formula_map().at(var);

  if (IsSimpleBound(formula)) {
    DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::EnableLinearLiteral({}{})", truth ? "" : "¬", formula);
    // bound = (variable, type, value), where:
    // - variable is the box variable
    // - type of bound
    // - value is the bound value
    Bound bound = GetBound(formula, truth);

    // Add the active bound to the LP solver bounds
    int theory_col = var_to_theory_col_[std::get<0>(bound).get_id()];
    bool valid_bound = SetSPXVarBound(bound, theory_col);
    theory_bound_to_explanation_[theory_col].insert(lit);
    // If the bound is invalid, return the explanation and update the SAT solver immediately
    if (!valid_bound) return theory_bound_to_explanation_[theory_col];
  }

  for (const Variable &row_var : formula.GetFreeVariables()) {
    var_to_enabled_theory_rows_.at(row_var.get_id()).push_back(spx_row);
  }

  const LpRowSense sense = truth ? spx_sense_[spx_row] : !spx_sense_[spx_row];
  const mpq_class &rhs{spx_rhs_[spx_row]};
  soplex::LPRowRational lp_row;
  spx_.getRowRational(spx_row, lp_row);
  soplex::DSVectorRational row_vector{lp_row.rowVector()};
  switch (sense) {
    case LpRowSense::LT:
      row_vector.add(strict_variable_idx(), 1);
      enabled_strict_theory_rows_.push_back(spx_row);
      break;
    case LpRowSense::GT:
      row_vector.add(strict_variable_idx(), -1);
      enabled_strict_theory_rows_.push_back(spx_row);
      break;
    case LpRowSense::EQ:
    case LpRowSense::LE:
    case LpRowSense::GE:
      row_vector.add(strict_variable_idx(), 0);
      break;
    case LpRowSense::NQ:
      row_vector.add(strict_variable_idx(), 1);
      nq_row_to_theory_rows_.push_back(spx_row);
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
  lp_row.setRowVector(row_vector);
  lp_row.setLhs(sense == LpRowSense::GE || sense == LpRowSense::EQ || sense == LpRowSense::GT
                    ? Rational(gmp::to_mpq_t(rhs))
                    : Rational(-soplex::infinity));
  lp_row.setRhs(sense == LpRowSense::LE || sense == LpRowSense::EQ || sense == LpRowSense::LT
                    ? Rational(gmp::to_mpq_t(rhs))
                    : Rational(soplex::infinity));
  spx_.changeRowRational(spx_row, lp_row);

  // Update the truth value for the current iteration with the last SAT solver assignment
  theory_row_to_truth_[spx_row] = truth;
  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::EnableLinearLiteral({}{})", truth ? "" : "¬", spx_row);
  return {};
}

bool CompleteSoplexTheorySolver::SetSPXVarBound(const Bound &bound, int spx_col) {
  const auto &[var, type, value] = bound;

  if (value <= -soplex::infinity || value >= soplex::infinity) {
    DLINEAR_RUNTIME_ERROR_FMT("Simple bound too large: {}", value);
  }

  if (type == LpColBound::B || type == LpColBound::L || type == LpColBound::SL) {
    if (gmp::to_mpq_t(value) > spx_lower_[spx_col]) {
      spx_lower_[spx_col] = gmp::to_mpq_t(value);
      DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::SetSPXVarBound ('{}'): set lower bound of {} to {}", type, var,
                        spx_lower_[spx_col]);
    }
  }
  if (type == LpColBound::B || type == LpColBound::U || type == LpColBound::SU) {
    if (gmp::to_mpq_t(value) < spx_upper_[spx_col]) {
      spx_upper_[spx_col] = gmp::to_mpq_t(value);
      DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::SetSPXVarBound ('{}'): set upper bound of {} to {}", type, var,
                        spx_upper_[spx_col]);
    }
  }
  // Make sure there are no inverted bounds
  if (spx_lower_[spx_col] > spx_upper_[spx_col]) {
    DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::SetSPXVarBound: variable {} has invalid bounds [{}, {}]", var,
                      spx_lower_[spx_col], spx_upper_[spx_col]);
    return false;
  }
  // If dealing with a strict inequality, put the exact value in the diff set for the column
  if (type == LpColBound::SL || type == LpColBound::SU || type == LpColBound::D) {
    spx_nq_.at(spx_col).insert(gmp::to_mpq_t(value));
  }
  if (spx_lower_[spx_col] == spx_upper_[spx_col] && spx_nq_.at(spx_col).count(spx_lower_[spx_col]) > 0) {
    DLINEAR_DEBUG_FMT(
        "CompleteSoplexTheorySolver::SetSPXVarBound: variable {} has invalid bounds [{}, {}] while dealing with a not "
        "equal bound",
        var, spx_lower_[spx_col], spx_upper_[spx_col]);
    return false;
  }
  return true;
}

SatResult CompleteSoplexTheorySolver::CheckSat(const Box &box, mpq_class *actual_precision, LiteralSet &explanation) {
  Consolidate();
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");

  static IterationStats stat{DLINEAR_INFO_ENABLED, "CompleteSoplexTheorySolver", "Total # of CheckSat",
                             "Total time spent in CheckSat"};
  TimerGuard check_sat_timer_guard(&stat.m_timer(), stat.enabled(), true /* start_timer */);
  stat.Increase();

  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::CheckSat: Box = \n{}", box);

  model_ = box;
  for (const Variable &var : theory_col_to_var_) {
    if (!model_.has_variable(var)) {
      // Variable should already be present
      DLINEAR_WARN_FMT("CompleteSoplexTheorySolver::CheckSat: Adding var {} to model from theory solver", var);
      model_.Add(var);
    }
  }

  // If we can immediately return SAT afterward
  if (spx_.numRowsRational() == 0) {
    DLINEAR_DEBUG("CompleteSoplexTheorySolver::CheckSat: no need to call LP solver");
    UpdateModelBounds();
    return SatResult::SAT_SATISFIABLE;
  }

  spx_.changeLowerRational(spx_lower_);
  spx_.changeUpperRational(spx_upper_);

  // Now we call the solver
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: calling SoPlex (phase {})",
                    1 == simplex_sat_phase_ ? "one" : "two");

  int colcount = spx_.numColsRational();
  explanation.clear();
  // TODO: iterate over all possible sub-problems
  // status (true -> less, false -> greater)
  BitIncrementIterator it(nq_row_to_theory_rows_.size());
  do {
    for (bool b : *it) {
      std::cout << b << " ";
    }
    SatResult sat_status = SpxCheckSat(actual_precision, explanation);

    soplex::VectorRational x;
    [[maybe_unused]] bool haveSoln;
    switch (sat_status) {
      case SatResult::SAT_SATISFIABLE:
        x.reDim(spx_.numColsRational());
        haveSoln = spx_.getPrimalRational(x);
        DLINEAR_ASSERT(haveSoln, "haveSoln must be true");
        DLINEAR_ASSERT(x.dim() >= colcount, "x.dim() must be >= colcount");
        if (x.dim() > colcount) {
          DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: colcount = {} but x.dim() = {}", colcount, x.dim());
        }
        // Copy delta-feasible point from x into model_
        for (int theory_col = 0; theory_col < static_cast<int>(theory_col_to_var_.size()); theory_col++) {
          const Variable &var{theory_col_to_var_[theory_col]};
          DLINEAR_ASSERT(model_[var].lb() <= gmp::to_mpq_class(x[theory_col].backend().data()) &&
                             gmp::to_mpq_class(x[theory_col].backend().data()) <= model_[var].ub(),
                         "val must be in bounds");
          model_[var] = x[theory_col].backend().data();
        }
        DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: returning {}", SatResult::SAT_SATISFIABLE);
        return SatResult::SAT_SATISFIABLE;
      default:
        DLINEAR_ASSERT(sat_status == SatResult::SAT_UNSATISFIABLE, "sat_status must be SAT_UNSATISFIABLE");
        break;
    }
  } while (++it);

  return SatResult::SAT_UNSATISFIABLE;
}

SatResult CompleteSoplexTheorySolver::SpxCheckSat(mpq_class *actual_precision, LiteralSet &explanation) {
  int colcount = spx_.numColsRational();
  SoplexStatus status = spx_.optimize();
  Rational max_violation, sum_violation;

  // If the simplex_sat_status is 2, we expect the status to be OPTIMAL
  // Otherwise, the status must be OPTIMAL, UNBOUNDED, or INFEASIBLE
  // Anything else is an error
  if ((2 == simplex_sat_phase_ && status != SoplexStatus::OPTIMAL) ||
      (status != SoplexStatus::OPTIMAL && status != SoplexStatus::UNBOUNDED && status != SoplexStatus::INFEASIBLE)) {
    DLINEAR_RUNTIME_ERROR_FMT("SoPlex returned {}. That's not allowed here", status);
  } else if (spx_.getRowViolationRational(max_violation, sum_violation)) {
    *actual_precision = mpq_class{max_violation.backend().data()};
    DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: SoPlex returned {}, precision = {}", status,
                      *actual_precision);
  } else {
    DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: SoPlex has returned {}, but no precision", status);
  }

  if (1 == simplex_sat_phase_) {
    switch (status) {
      case SoplexStatus::OPTIMAL:
        if (spx_.objValueRational() > 0) return SatResult::SAT_SATISFIABLE;
        if (explanation.empty()) UpdateExplanationStrict(explanation);
        return SatResult::SAT_UNSATISFIABLE;
      case SoplexStatus::INFEASIBLE:
        if (explanation.empty()) UpdateExplanation(explanation);
        return SatResult::SAT_UNSATISFIABLE;
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
    soplex::VectorRational x{colcount};
    [[maybe_unused]] bool haveSoln = spx_.getPrimalRational(x);
    DLINEAR_ASSERT(haveSoln, "haveSoln must be true");
    DLINEAR_ASSERT(x.dim() >= colcount, "x.dim() must be >= colcount");
    if (x.dim() > colcount) {
      DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: colcount = {} but x.dim() = {}", colcount, x.dim());
    }
    // ok = std::ranges::all_of(0, colcount, [&] (int i) { return obj[i] == 0 || x[i] == 0; });
    for (int i = 0; i < colcount; ++i) {
      if (!(ok = (obj[i] == 0 || x[i] == 0))) {
        break;
      }
    }
    if (ok) return SatResult::SAT_SATISFIABLE;
    return SatResult::SAT_UNSATISFIABLE;
  }
}

void CompleteSoplexTheorySolver::Reset(const Box &box) {
  SoplexTheorySolver::Reset(box);
  for (auto &diff : spx_nq_) diff.clear();
  for (auto &rows : var_to_enabled_theory_rows_) rows.second.clear();
  enabled_strict_theory_rows_.clear();
  nq_row_to_theory_rows_.clear();
}

void CompleteSoplexTheorySolver::Consolidate() {
  if (is_consolidated_) return;
  SoplexTheorySolver::Consolidate();
  // Reserve memory for all possible active strict theory rows
  enabled_strict_theory_rows_.reserve(spx_.numRowsRational());
  const int spx_col = spx_.numColsRational();
  spx_lower_.reDim(spx_col + 1, false);
  spx_upper_.reDim(spx_col + 1, false);
  spx_lower_[spx_col] = 0;
  spx_upper_[spx_col] = 1;
  // Column of the strict auxiliary variable t bound between 0 and 1
  spx_.addColRational(soplex::LPColRational(0, soplex::DSVectorRational(), 1, 0));
  spx_.changeObjRational(spx_col, 1);
  DLINEAR_DEBUG("CompleteSoplexTheorySolver::InitCheckSat: initialised");
}

int CompleteSoplexTheorySolver::strict_variable_idx() const {
  DLINEAR_ASSERT(is_consolidated_, "The solver must be initialised for the strict variable to be present");
  return spx_.numColsRational() - 1;
}

// TODO: implement cache between first GetActiveRows call and the second one to keep track of rows in
// enabled_strict_theory_rows_
void CompleteSoplexTheorySolver::UpdateExplanationStrict(LiteralSet &explanation) {
  DLINEAR_TRACE("CompleteSoplexTheorySolver::UpdateExplanationStrict");
  explanation.clear();
  // Active row: the difference between (solution vector X the row's coefficients) and (lhs/rhs) value is 0
  // Find all strict theory row. The active ones indicate a violation in the strict bound.
  std::set<int> candidate_rows;
  std::vector<Variable::Id> stack;
  std::set<Variable::Id> visited_variables;
  for (const auto &[spx_row, value] : GetActiveRows(enabled_strict_theory_rows_)) {
    // Find all the free variables in the row
    const auto &row_formula = predicate_abstractor_.var_to_formula_map().find(theory_row_to_lit_[spx_row])->second;
    DLINEAR_ASSERT(!row_formula.GetFreeVariables().empty(), "row_formula.GetFreeVariables() must not be empty");
    for (const Variable &var : row_formula.GetFreeVariables()) {
      // Add all the free variables to the set of variables to check for active constraints
      if (visited_variables.count(var.get_id()) > 0) continue;
      stack.push_back(var.get_id());
      visited_variables.insert(var.get_id());
    }
  }

  // Run through the variables in the stack and add to the candidate violated rows all rows they appear in
  while (!stack.empty()) {
    Variable::Id var_id = stack.back();
    stack.pop_back();

    for (int spx_row : var_to_enabled_theory_rows_.at(var_id)) {
      candidate_rows.insert(spx_row);
      // Also add the free variables not yet visited in that row to the stack to check them later
      const auto &row_formula = predicate_abstractor_.var_to_formula_map().find(theory_row_to_lit_[spx_row])->second;
      for (const Variable &var : row_formula.GetFreeVariables()) {
        if (visited_variables.count(var.get_id()) > 0) continue;
        stack.push_back(var.get_id());
        visited_variables.insert(var.get_id());
      }
    }
  }

  // Add all active rows in the candidate rows to the explanation
  for (const auto &[spx_row, value] : GetActiveRows({candidate_rows.begin(), candidate_rows.end()})) {
    explanation.insert({theory_row_to_lit_[spx_row], theory_row_to_truth_[spx_row]});
  }

  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::UpdateExplanationStrict: explanation = {}", explanation);
}
}  // namespace dlinear
