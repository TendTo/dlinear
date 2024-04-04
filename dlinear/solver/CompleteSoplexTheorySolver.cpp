/**
 * @file CompleteSoplexTheorySolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "CompleteSoplexTheorySolver.h"

#include <map>
#include <stack>
#include <utility>

#include "dlinear/libs/soplex.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

using SoplexStatus = soplex::SPxSolver::Status;
using soplex::Rational;

const mpq_class CompleteSoplexTheorySolver::strict_col_lb_{0};
const mpq_class CompleteSoplexTheorySolver::strict_col_ub_{1};

CompleteSoplexTheorySolver::CompleteSoplexTheorySolver(PredicateAbstractor &predicate_abstractor,
                                                       const std::string &class_name)
    : SoplexTheorySolver(predicate_abstractor, class_name),
      enabled_strict_theory_rows_{},
      var_to_enabled_theory_rows_{},
      nq_row_to_theory_rows_{},
      last_nq_status_{},
      theory_rows_to_explanation_{} {
  DLINEAR_ASSERT(config_.precision() == 0, "CompleteSoplexTheorySolver does not support a positive precision");
}

void CompleteSoplexTheorySolver::AddVariable(const Variable &var) {
  auto it = var_to_theory_col_.find(var.get_id());
  // The variable is already present
  if (it != var_to_theory_col_.end()) return;
  SoplexTheorySolver::AddVariable(var);
  // Add the set of differences for the new variable that will map to a column of the LP problem
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
  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::AddLinearLiteral: {} -> {}", formula, spx_sense_.back());

  const int spx_row{spx_.numRowsRational()};

  // Add an inactive constraint with the right coefficients for the decisional variables
  soplex::DSVectorRational coeffs{ParseRowCoeff(formula)};
  spx_.addRowRational(soplex::LPRowRational(-soplex::infinity, coeffs, soplex::infinity));
  if (2 == config_.simplex_sat_phase()) CreateArtificials(spx_row);

  // Update indexes
  lit_to_theory_row_.emplace(formulaVar.get_id(), spx_row);
  theory_row_to_lit_.emplace_back(formulaVar, true);
  last_nq_status_.push_back(false);

  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == theory_row_to_lit_.size() - 1, "incorrect theory_row_to_lit_.size()");
  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == spx_sense_.size() - 1, "incorrect spx_sense_.size()");
  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == spx_rhs_.size() - 1, "incorrect spx_rhs_.size()");
  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == last_nq_status_.size() - 1, "incorrect spx_rhs_.size()");
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::AddLinearLiteral({} ↦ {})", it->second, spx_row);
}

CompleteSoplexTheorySolver::Explanations CompleteSoplexTheorySolver::EnableLiteral(const Literal &lit) {
  Consolidate();
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");

  const auto &[var, truth] = lit;
  const auto it_row = lit_to_theory_row_.find(var.get_id());

  // If the literal was not already among the constraints (rows) of the LP, it must be a learned literal.
  if (it_row == lit_to_theory_row_.end()) {
    DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::EnableLinearLiteral: ignoring ({})", lit);
    return {};
  }

  // A non-trivial linear literal from the input problem
  const int spx_row = it_row->second;
  // Update the truth value for the current iteration with the last SAT solver assignment
  theory_row_to_lit_[spx_row].truth = truth;
  // Add the row to the list of enabled theory rows
  enabled_theory_rows_.push_back(spx_row);

  // Enable the row in the preprocessor
  preprocessor_.EnableConstraint(spx_row);

  DLINEAR_ASSERT(predicate_abstractor_.var_to_formula_map().count(var) != 0, "var must map to a theory literal");
  const Formula &formula = predicate_abstractor_[var];
  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::EnableLinearLiteral({}{})", truth ? "" : "¬", formula);

  // If it is a simple bound, we add it to the theory_bounds.
  // Later, active strict bounds will also appear in the LP problem as strict rows
  if (IsSimpleBound(formula)) {
    // bound = (variable, type, value), where:
    // - variable is the box variable
    // - type of bound
    // - value is the bound value
    auto [b_var, type, value] = GetBound(formula, truth);
    DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::EnableLinearLiteral: bound ({}, {} {})", b_var, type, value);

    // Add the active bound to the LP solver bounds
    int theory_col = var_to_theory_col_[b_var.get_id()];
    const TheorySolverBoundVector::BoundIterator violation{theory_bounds_[theory_col].AddBound(value, type, spx_row)};

    // If the bound is invalid, return the explanation and update the SAT solver immediately
    if (violation) return TheoryBoundsToExplanations(violation, spx_row);
    return {};
  }

  EnableSpxRow(spx_row, truth, formula.GetFreeVariables());
  return {};
}

SatResult CompleteSoplexTheorySolver::CheckSat(const Box &box, mpq_class *actual_precision,
                                               Explanations &explanations) {
  Consolidate();
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");

  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();

  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::CheckSat: Box = \n{}", box);

  model_ = box;
  DLINEAR_ASSERT(std::all_of(theory_col_to_var_.begin(), theory_col_to_var_.end(),
                             [&box](const Variable &var) { return box.has_variable(var); }),
                 "All theory variables must be present in the box");

  // If we can immediately return SAT afterward
  if (spx_.numRowsRational() == 0) {
    DLINEAR_DEBUG("CompleteSoplexTheorySolver::CheckSat: no need to call LP solver");
    UpdateModelBounds();
    return SatResult::SAT_SATISFIABLE;
  }

  // Preprocess the constraints
  preprocessor_.Process(enabled_theory_rows_, explanations);
  if (!explanations.empty()) return SatResult::SAT_UNSATISFIABLE;

  // Set the bounds for the variables
  EnableSPXVarBound();

  // Now we call the solver
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: calling SoPlex (phase {})", config_.simplex_sat_phase());

  SatResult sat_status;
  // Initialise the iterator with the last nq statuses
  std::vector<bool> starting_iterator(nq_row_to_theory_rows_.size(), false);
  std::transform(nq_row_to_theory_rows_.cbegin(), nq_row_to_theory_rows_.cend(), starting_iterator.begin(),
                 [&](int i) { return last_nq_status_[i]; });
  BitIncrementIterator it(starting_iterator);
  do {
    // Enable the non-equal constraints based on the current iterator value.
    // If the iterator is empty (there are no not-equal constraints), this will do nothing
    EnableNqLiterals(*it);

    // Solve the sub-problem
    sat_status = SpxCheckSat(actual_precision);
    DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::CheckSat: intermediate sat_status = {}", sat_status);

    // If the problem is SAT, we can return immediately
    if (sat_status == SatResult::SAT_SATISFIABLE) break;

    // Use some heuristics to update the iterator based on the current explanation.
    // Otherwise, just increment the iterator with the next configuration and try again
    if (!UpdateBitIncrementIteratorBasedOnExplanation(it)) break;
  } while (it);

  soplex::VectorRational x;
  [[maybe_unused]] bool has_sol;
  const int colcount = spx_.numColsRational();
  switch (sat_status) {
    case SatResult::SAT_SATISFIABLE:
      x.reDim(spx_.numColsRational());
      has_sol = spx_.getPrimalRational(x);
      DLINEAR_ASSERT(has_sol, "has_sol must be true");
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
    case SatResult::SAT_UNSATISFIABLE:
      DLINEAR_TRACE("CompleteSoplexTheorySolver::CheckSat: all options explored, returning unsat");
      GetExplanation(explanations);
      return SatResult::SAT_UNSATISFIABLE;
    default:
      DLINEAR_UNREACHABLE();
  }
}

SatResult CompleteSoplexTheorySolver::SpxCheckSat(mpq_class *actual_precision) {
  int colcount = spx_.numColsRational();
  SoplexStatus status = spx_.optimize();
  Rational max_violation, sum_violation;

  // If the simplex_sat_status is 2, we expect the status to be OPTIMAL
  // Otherwise, the status must be OPTIMAL, UNBOUNDED, or INFEASIBLE
  // Anything else is an error
  if ((2 == config_.simplex_sat_phase() && status != SoplexStatus::OPTIMAL) ||
      (status != SoplexStatus::OPTIMAL && status != SoplexStatus::UNBOUNDED && status != SoplexStatus::INFEASIBLE)) {
    DLINEAR_RUNTIME_ERROR_FMT("SoPlex returned {}. That's not allowed here", status);
  } else if (spx_.getRowViolationRational(max_violation, sum_violation)) {
    *actual_precision = mpq_class{max_violation.backend().data()};
    DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: SoPlex returned {}, precision = {}", status,
                      *actual_precision);
  } else {
    DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: SoPlex has returned {}, but no precision", status);
  }

  if (1 == config_.simplex_sat_phase()) {
    switch (status) {
      case SoplexStatus::OPTIMAL:
        if (spx_.objValueRational() > 0) return SatResult::SAT_SATISFIABLE;
        UpdateExplanationStrictInfeasible();
        return SatResult::SAT_UNSATISFIABLE;
      case SoplexStatus::INFEASIBLE:
        UpdateExplanationInfeasible();
        return SatResult::SAT_UNSATISFIABLE;
      default:
        DLINEAR_UNREACHABLE();
    }
  } else {
    // The feasibility LP should always be feasible & bounded
    DLINEAR_ASSERT(status == SoplexStatus::OPTIMAL, "status must be OPTIMAL");
    [[maybe_unused]] soplex::VectorRational obj;
    spx_.getObjRational(obj);
    DLINEAR_ASSERT(obj.dim() == colcount, "obj.dim() must be == colcount");
    soplex::VectorRational x{colcount};
    [[maybe_unused]] const bool has_sol = spx_.getPrimalRational(x);
    DLINEAR_ASSERT(has_sol, "has_sol must be true");
    DLINEAR_ASSERT(x.dim() >= colcount, "x.dim() must be >= colcount");
    if (x.dim() > colcount) {
      DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: colcount = {} but x.dim() = {}", colcount, x.dim());
    }
    // Check if the strict variable is positive (feasible) or 0 (infeasible)
    DLINEAR_ASSERT(obj[colcount - 1] == 1, "The strict variable must have a coefficient of 1 in the objective");
    if (x[colcount - 1].is_zero()) return SatResult::SAT_UNSATISFIABLE;
    return SatResult::SAT_SATISFIABLE;
  }
}

void CompleteSoplexTheorySolver::Reset(const Box &box) {
  SoplexTheorySolver::Reset(box);
  for (auto &rows : var_to_enabled_theory_rows_) rows.second.clear();
  enabled_strict_theory_rows_.clear();
  nq_row_to_theory_rows_.clear();
  theory_rows_to_explanation_.clear();
}

void CompleteSoplexTheorySolver::Consolidate() {
  if (is_consolidated_) return;
  SoplexTheorySolver::Consolidate();
  // Reserve memory for all possible active strict theory rows
  enabled_strict_theory_rows_.reserve(spx_.numRowsRational());
  const int spx_col = spx_.numColsRational();
  theory_bounds_.emplace_back(strict_col_lb_, strict_col_ub_);
  // Column of the strict auxiliary variable t bound between 0 and 1
  spx_.addColRational(soplex::LPColRational(0, soplex::DSVectorRational(), 1, 0));
  spx_.changeObjRational(spx_col, 1);

  [[maybe_unused]] const auto rowcount = static_cast<size_t>(spx_.numRowsRational());
  [[maybe_unused]] const auto colcount = static_cast<size_t>(spx_.numColsRational());
  DLINEAR_ASSERT(colcount == theory_col_to_var_.size() + 1, "incorrect theory_col_to_var_.size()");
  DLINEAR_ASSERT(colcount == var_to_theory_col_.size() + 1, "incorrect var_to_theory_col_.size()");
  DLINEAR_ASSERT(colcount == theory_bounds_.size(), "incorrect theory_bounds_.size()");
  DLINEAR_ASSERT(rowcount == spx_sense_.size(), "incorrect spx_sense_.size()");
  DLINEAR_ASSERT(rowcount == spx_rhs_.size(), "incorrect spx_rhs_.size()");
  DLINEAR_ASSERT(rowcount == last_nq_status_.size(), "incorrect spx_rhs_.size()");
  DLINEAR_ASSERT(rowcount == theory_row_to_lit_.size(), "incorrect theory_row_to_lit_.size()");
  DLINEAR_DEBUG("CompleteSoplexTheorySolver::Consolidate: consolidated");
}

int CompleteSoplexTheorySolver::strict_variable_idx() const {
  DLINEAR_ASSERT(is_consolidated_, "The solver must be initialised for the strict variable to be present");
  return spx_.numColsRational() - 1;
}

void CompleteSoplexTheorySolver::EnableNqLiterals(const std::vector<bool> &nq_status) {
  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::EnableNqLiterals: nq_status = {}", nq_status);
  for (size_t i = 0; i < nq_status.size(); i++) {
    const int &spx_row = nq_row_to_theory_rows_[i];
    // The row's sense has not changed since last time, skip
    if (last_nq_status_[spx_row] == nq_status[i]) continue;
    last_nq_status_[spx_row] = nq_status[i];

    const Rational rhs{spx_rhs_[spx_row].get_mpq_t()};

    soplex::LPRowRational lp_row(spx_.numColsRational());
    spx_.getRowRational(spx_row, lp_row);
    soplex::DSVectorRational row_vector{lp_row.rowVector()};

    const int pos = row_vector.pos(strict_variable_idx());
    DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::EnableNqLiterals: Row({}) ↦ {} {} {}", spx_row, lp_row.lhs(),
                      lp_row.rowVector(), lp_row.rhs());
    DLINEAR_ASSERT(!row_vector.value(pos).is_zero(), "Coefficient of the strict auxiliary variable cannot be 0");
    row_vector.value(pos) = nq_status[i] ? -1 : 1;

    lp_row.setLhs(nq_status[i] ? rhs : -soplex::infinity);
    lp_row.setRhs(nq_status[i] ? soplex::infinity : rhs);
    lp_row.setRowVector(row_vector);

    spx_.changeRowRational(spx_row, lp_row);
  }
}

void CompleteSoplexTheorySolver::UpdateExplanationInfeasible() {
  soplex::VectorRational ray{spx_.numRowsRational()};
  std::vector<BoundViolationType> bounds_ray(spx_.numColsRational() - 1, BoundViolationType::NO_BOUND_VIOLATION);
  GetSpxInfeasibilityRay(ray, bounds_ray);

  theory_rows_to_explanation_.clear();
  // For each row in the ray
  for (int i = 0; i < spx_.numRowsRational(); ++i) {
    if (ray[i].is_zero()) continue;  // The row did not participate in the conflict, ignore it
    DLINEAR_TRACE_FMT("SoplexSatSolver::UpdateExplanation: ray[{}] = {}", i, ray[i]);
    // Insert the conflicting row literal to the explanation
    theory_rows_to_explanation_.insert(i);

    // Add all the active bounds for the free variables in the row to the explanation
    const auto &row_formula = predicate_abstractor_[theory_row_to_lit_[i].var];
    for (const Variable &var : row_formula.GetFreeVariables()) {
      const int &theory_col = var_to_theory_col_.at(var.get_id());
      TheoryBoundsToBoundIdxs(theory_col, bounds_ray[theory_col], theory_rows_to_explanation_);
    }
  }

  DLINEAR_ASSERT(!theory_rows_to_explanation_.empty(), "theory_rows_to_explanation_ must contain at least a violation");
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::UpdateExplanationInfeasible: ↦ {}", theory_rows_to_explanation_);
}

void CompleteSoplexTheorySolver::UpdateExplanationStrictInfeasible() {
  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::UpdateExplanationStrictInfeasible({})", enabled_strict_theory_rows_);
  DLINEAR_ASSERT(!enabled_strict_theory_rows_.empty(), "enabled_strict_theory_rows_ must not be empty");
  DLINEAR_ASSERT(!GetActiveRows(enabled_strict_theory_rows_).empty(), "At least 1 strict row must have been  violated");

  // Clear previous explanation
  theory_rows_to_explanation_.clear();

  // Solution vector. Contains the value of all the variables
  soplex::VectorRational x{spx_.numColsRational()};
  [[maybe_unused]] bool has_sol = spx_.getPrimalRational(x);
  DLINEAR_ASSERT(has_sol, "has_sol must be true");
  soplex::VectorRational dual{spx_.numRowsRational()};
  [[maybe_unused]] const bool has_dual = spx_.getDualRational(dual);
  DLINEAR_ASSERT(has_dual, "has_dual must be true");

  // Active row: the difference between (solution vector X the row's coefficients) and (lhs/rhs) value is 0
  // Find all strict theory row. The active ones indicate a violation in the strict bound.
  std::set<Variable::Id> visited_variables;
  for (int i = 0; i < dual.dim(); ++i) {
    // Skip inactive rows
    if (dual[i].is_zero()) continue;

    enabled_strict_theory_rows_.push_back(i);
    theory_rows_to_explanation_.insert(i);
    const auto &row_formula = predicate_abstractor_[theory_row_to_lit_[i].var];
    for (const Variable &var : row_formula.GetFreeVariables()) visited_variables.insert(var.get_id());
  }

  DLINEAR_DEBUG_FMT("Strict active rows: {}", theory_rows_to_explanation_);

  // Run through the variables found in the active rows
  for (const Variable::Id &var_id : visited_variables) {
    // Add all the bounds for the variable to explanation, if they are active
    const int theory_col = var_to_theory_col_.at(var_id);
    TheoryBoundsToBoundIdxs(theory_col, mpq_class{x[theory_col].backend().data()}, theory_rows_to_explanation_);
  }

  DLINEAR_ASSERT(!theory_rows_to_explanation_.empty(), "theory_rows_to_explanation_ must contain at least a violation");
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::UpdateExplanationStrictInfeasible: ↦ {}", theory_rows_to_explanation_);
}

void CompleteSoplexTheorySolver::GetExplanation(Explanations &explanations) {
  DLINEAR_ASSERT(!theory_rows_to_explanation_.empty(), "theory_rows_to_explanation_ must contain at least a violation");
  LiteralSet explanation;
  GetExplanation(explanation);
  explanations.insert(explanation);
}
void CompleteSoplexTheorySolver::GetExplanation(LiteralSet &explanation) {
  DLINEAR_ASSERT(!theory_rows_to_explanation_.empty(), "theory_rows_to_explanation_ must contain at least a violation");
  explanation.clear();
  for (const auto &spx_row : theory_rows_to_explanation_) {
    explanation.insert(theory_row_to_lit_[spx_row]);
  }
}

std::vector<size_t> CompleteSoplexTheorySolver::IteratorNqRowsInExplanation() const {
  std::vector<size_t> nq_row_to_iterator_index;
  for (size_t i = 0; i < nq_row_to_theory_rows_.size(); i++) {
    const int &spx_row = nq_row_to_theory_rows_[i];
    if (theory_rows_to_explanation_.find(spx_row) != theory_rows_to_explanation_.end()) {
      nq_row_to_iterator_index.push_back(i);
    }
  }
  return nq_row_to_iterator_index;
}

bool CompleteSoplexTheorySolver::UpdateBitIncrementIteratorBasedOnExplanation(BitIncrementIterator &bit_iterator) {
  // No explanation yet
  if (theory_rows_to_explanation_.empty()) return true;

  std::vector<size_t> nq_in_explanation = IteratorNqRowsInExplanation();
  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::CheckSat: nq_in_explanation = {}", nq_in_explanation);
  // If no non-equal is violated, we can return immediately since the problem is UNSAT for other reasons
  if (nq_in_explanation.empty()) {
    DLINEAR_DEBUG("CompleteSoplexTheorySolver::CheckSat: no non-equal rows in explanation. Infeasibility detected");
    return false;
  }
  // If there is just a single non-equal row in the explanation...
  if (nq_in_explanation.size() == 1) {
    DLINEAR_TRACE("CompleteSoplexTheorySolver::CheckSat: only one non-equal row in explanation. Updating iterator");
    DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: the row was{} fixed before",
                      bit_iterator.IsFixed(nq_in_explanation.back()) ? "" : " NOT");
    // ... if it is the first time this happens, skip to an iterator values that doesn't violate the row anymore
    // otherwise, it meas that this row cannot be satisfied by the current model, so we can return immediately
    return bit_iterator.Learn(nq_in_explanation.back());
  }
  // No heuristics to update the iterator based on the current explanation, so just increment the iterator
  ++bit_iterator;
  return true;
}

void CompleteSoplexTheorySolver::EnableSPXVarBound() {
  SoplexTheorySolver::EnableSPXVarBound();
  // For all columns...
  for (const auto &theory_bound : theory_bounds_) {
    // ... for each active bound of that column...
    for (TheorySolverBoundVector::BoundIterator it{theory_bound.GetActiveBound()}; it; ++it) {
      const auto &[value, bound, spx_row] = *it;
      // ... if we are dealing with a strict bound, add the strict row to the LP problem
      if (bound == LpColBound::SU || bound == LpColBound::SL || bound == LpColBound::D) {
        SoplexTheorySolver::EnableSpxRow(spx_row);
      }
    }
  }
}

void CompleteSoplexTheorySolver::EnableSpxRow(int spx_row, bool truth, const Variables &free_vars) {
  for (const Variable &row_var : free_vars) {
    var_to_enabled_theory_rows_.at(row_var.get_id()).push_back(spx_row);
  }

  const LpRowSense sense = truth ? spx_sense_[spx_row] : !spx_sense_[spx_row];
  const mpq_class &rhs{spx_rhs_[spx_row]};
  soplex::LPRowRational lp_row;
  spx_.getRowRational(spx_row, lp_row);
  soplex::DSVectorRational row_vector{lp_row.rowVector()};
  // Remove the strict variable from the row and add it back with the right coefficient
  int pos = row_vector.pos(strict_variable_idx());
  if (pos < 0) {
    row_vector.add(strict_variable_idx(), 1);
    pos = row_vector.pos(strict_variable_idx());
  }
  switch (sense) {
    case LpRowSense::LT:
      row_vector.value(pos) = 1;
      enabled_strict_theory_rows_.push_back(spx_row);
      break;
    case LpRowSense::GT:
      row_vector.value(pos) = -1;
      enabled_strict_theory_rows_.push_back(spx_row);
      break;
    case LpRowSense::EQ:
    case LpRowSense::LE:
    case LpRowSense::GE:
      row_vector.value(pos) = 0;
      break;
    case LpRowSense::NQ:
      // Initialise the inequality based on the last status stored ( < or > )
      row_vector.value(pos) = last_nq_status_[spx_row] ? -1 : 1;
      enabled_strict_theory_rows_.push_back(spx_row);
      nq_row_to_theory_rows_.push_back(spx_row);
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
  lp_row.setRowVector(row_vector);
  lp_row.setLhs(sense == LpRowSense::GE || sense == LpRowSense::EQ || sense == LpRowSense::GT ||
                        (sense == LpRowSense::NQ && last_nq_status_[spx_row])
                    ? Rational(gmp::to_mpq_t(rhs))
                    : Rational(-soplex::infinity));
  lp_row.setRhs(sense == LpRowSense::LE || sense == LpRowSense::EQ || sense == LpRowSense::LT ||
                        (sense == LpRowSense::NQ && !last_nq_status_[spx_row])
                    ? Rational(gmp::to_mpq_t(rhs))
                    : Rational(soplex::infinity));
  spx_.changeRowRational(spx_row, lp_row);

  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::EnableLinearLiteral: Row({}) ↦ {} {} {} | Sense({})", spx_row,
                    lp_row.lhs(), lp_row.rowVector(), lp_row.rhs(), sense);
}

}  // namespace dlinear
