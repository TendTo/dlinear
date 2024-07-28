/**
 * @file CompleteSoplexTheorySolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
// IWYU pragma: no_include <new>
#include "CompleteSoplexTheorySolver.h"

#include <algorithm>
#include <map>
#include <unordered_map>
#include <utility>

#include "dlinear/libs/libsoplex.h"
#include "dlinear/solver/LpColBound.h"
#include "dlinear/solver/LpRowSense.h"
#include "dlinear/solver/TheorySolverBoundIterator.h"
#include "dlinear/solver/TheorySolverBoundPreprocessor.h"
#include "dlinear/solver/TheorySolverBoundVector.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

#define STRICT_VARIABLE_IDX (spx_.numColsRational() - 1)

namespace dlinear {

namespace {

inline size_t bool_vector_to_int(const std::vector<bool> &v, const std::set<size_t> &positions) {
  size_t result = 0;
  for (const size_t &pos : positions) {
    result <<= 1;
    result |= v.at(pos);
  }
  return result;
}

}  // namespace

using SoplexStatus = soplex::SPxSolver::Status;
using soplex::Rational;

const mpq_class CompleteSoplexTheorySolver::strict_col_lb_{0};
const mpq_class CompleteSoplexTheorySolver::strict_col_ub_{1};

CompleteSoplexTheorySolver::CompleteSoplexTheorySolver(PredicateAbstractor &predicate_abstractor,
                                                       const std::string &class_name)
    : SoplexTheorySolver(predicate_abstractor, class_name),
      nq_row_to_theory_rows_{},
      last_nq_status_{},
      last_theory_rows_to_explanation_{},
      theory_rows_to_explanations_{},
      locked_solver_{false} {
  DLINEAR_ASSERT(config_.precision() == 0, "CompleteSoplexTheorySolver does not support a positive precision");
}

void CompleteSoplexTheorySolver::AddVariable(const Variable &var) {
  auto it = var_to_theory_col_.find(var.get_id());
  // The variable is already present
  if (it != var_to_theory_col_.end()) return;
  SoplexTheorySolver::AddVariable(var);
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

  spx_sense_.push_back(parseLpSense(formula));
  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::AddLinearLiteral: {} -> {}", lit, spx_sense_.back());

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
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::AddLinearLiteral({} ↦ {})", lit, spx_row);
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

  EnableSpxRow(spx_row, truth);
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
  // Remove all the disabled rows from the LP solver
  DisableSpxRows();

  // Now we call the solver
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: calling SoPlex (phase {})", config_.simplex_sat_phase());

  SatResult sat_status;

  // First, check the sat result without taking into account nq constraints
  sat_status = SpxCheckSat();
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: no nq constraints sat_status = {}", sat_status);
  if (sat_status != SatResult::SAT_SATISFIABLE) {
    theory_rows_to_explanations_.insert(last_theory_rows_to_explanation_);
    DLINEAR_ASSERT(theory_rows_to_explanations_.size() == 1, "theory_rows_to_explanations_ must have size 1");
    GetExplanation(explanations);
    return sat_status;
  }

  // Initialise the iterator with the last nq statuses
  std::vector<bool> starting_iterator(nq_row_to_theory_rows_.size(), false);
  for (size_t i = 0; i < nq_row_to_theory_rows_.size(); i++) {
    starting_iterator[i] = last_nq_status_[nq_row_to_theory_rows_[i]];
  }
  BitIncrementIterator it(starting_iterator);
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: nq starting iterator size = {}", starting_iterator.size());
  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::CheckSat: nq starting iterator = {}", it);

  // Ensure that all non-equal constraints are enabled based on the current iterator value
  EnableNqLiterals(starting_iterator, true);
  do {
    // Clean up the last explanation
    last_theory_rows_to_explanation_.clear();

    // Enable the non-equal constraints based on the current iterator value.
    // If the iterator is empty (there are no not-equal constraints), this will do nothing
    EnableNqLiterals(*it);

    // Omitting to do this seems to cause problems in soplex
    spx_.clearBasis();

    // Solve the sub-problem
    sat_status = SpxCheckSat();
    DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::CheckSat: intermediate sat_status = {}", sat_status);

    // If the problem is SAT and not locked, we can return immediately
    if (sat_status == SatResult::SAT_SATISFIABLE) break;

    // Use some heuristics to update the iterator based on the current explanation.
    // Otherwise, just increment the iterator with the next configuration and try again
    if (!UpdateBitIncrementIteratorBasedOnExplanation(it)) break;
  } while (it);

  *actual_precision = 0;
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
      DLINEAR_DEBUG("CompleteSoplexTheorySolver::CheckSat: returning sat");
      return SatResult::SAT_SATISFIABLE;
    case SatResult::SAT_UNSATISFIABLE:
      GetExplanation(explanations);
      DLINEAR_DEBUG("CompleteSoplexTheorySolver::CheckSat: returning unsat");
      return SatResult::SAT_UNSATISFIABLE;
    default:
      DLINEAR_UNREACHABLE();
  }
}

SatResult CompleteSoplexTheorySolver::SpxCheckSat() {
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
    DLINEAR_ASSERT(max_violation.is_zero(), "max_violation must be 0");
    DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: SoPlex returned {}, precision = 0", status);
  } else {
    DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: SoPlex has returned {}, but no precision", status);
  }

  if (1 == config_.simplex_sat_phase()) {
    switch (status) {
      case SoplexStatus::OPTIMAL:
        if (spx_.objValueRational() > 0)
          return locked_solver_ ? SatResult::SAT_UNSATISFIABLE : SatResult::SAT_SATISFIABLE;
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
    return locked_solver_ ? SatResult::SAT_UNSATISFIABLE : SatResult::SAT_SATISFIABLE;
  }
}

void CompleteSoplexTheorySolver::Reset(const Box &box) {
  SoplexTheorySolver::Reset(box);
  nq_row_to_theory_rows_.clear();
  theory_rows_to_explanations_.clear();
  nq_explanations_.clear();
  locked_solver_ = false;
  last_theory_rows_to_explanation_.clear();
  single_nq_rows_.clear();
}

void CompleteSoplexTheorySolver::Consolidate() {
  if (is_consolidated_) return;
  SoplexTheorySolver::Consolidate();
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

void CompleteSoplexTheorySolver::EnableNqLiteral(const int spx_row, const bool truth) {
  last_nq_status_[spx_row] = truth;

  const Rational rhs{spx_rhs_[spx_row].get_mpq_t()};

  soplex::LPRowRational lp_row(spx_.numColsRational());
  spx_.getRowRational(spx_row, lp_row);
  soplex::DSVectorRational row_vector{lp_row.rowVector()};

  const int pos = row_vector.pos(STRICT_VARIABLE_IDX);
  DLINEAR_ASSERT(!row_vector.value(pos).is_zero(), "Coefficient of the strict auxiliary variable cannot be 0");
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::EnableNqLiterals: Row({}) ↦ {} {} {}", spx_row, lp_row.lhs(),
                    lp_row.rowVector(), lp_row.rhs());

  row_vector.value(pos) = truth ? -1 : 1;

  lp_row.setLhs(truth ? rhs : -soplex::infinity);
  lp_row.setRhs(truth ? soplex::infinity : rhs);
  lp_row.setRowVector(row_vector);

  spx_.changeRowRational(spx_row, lp_row);
}

void CompleteSoplexTheorySolver::EnableNqLiterals(const std::vector<bool> &nq_status, const bool force) {
  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::EnableNqLiterals: nq_status = {}, force? = {}", nq_status, force);
  for (size_t i = 0; i < nq_status.size(); i++) {
    const int &spx_row = nq_row_to_theory_rows_[i];
    // The row's sense has not changed since last time and the row is not in forced_nq_constraints, skip
    if (last_nq_status_[spx_row] == nq_status[i] && !force) continue;
    EnableNqLiteral(spx_row, nq_status[i]);
  }
}

void CompleteSoplexTheorySolver::DisableNqLiterals(const std::set<size_t> &nq_constraints) {
  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::DisableNqLiterals: nq_constraints = {}", nq_constraints);
  for (const size_t i : nq_constraints) {
    const int &spx_row = nq_row_to_theory_rows_[i];
    spx_.changeRangeRational(spx_row, -soplex::infinity, soplex::infinity);
  }
}

void CompleteSoplexTheorySolver::UpdateExplanationInfeasible() {
  DLINEAR_ASSERT(last_theory_rows_to_explanation_.empty(), "last explanation must be empty");
  soplex::VectorRational ray{spx_.numRowsRational()};
  std::vector<BoundViolationType> bounds_ray(spx_.numColsRational() - 1, BoundViolationType::NO_BOUND_VIOLATION);
  GetSpxInfeasibilityRay(ray, bounds_ray);

  // For each row in the ray
  for (int i = 0; i < spx_.numRowsRational(); ++i) {
    if (ray[i].is_zero()) continue;  // The row did not participate in the conflict, ignore it
    DLINEAR_TRACE_FMT("SoplexSatSolver::UpdateExplanation: ray[{}] = {}", i, ray[i]);
    // Insert the conflicting row literal to the explanation
    last_theory_rows_to_explanation_.insert(i);

    // Add all the active bounds for the free variables in the row to the explanation
    const auto &row_formula = predicate_abstractor_[theory_row_to_lit_[i].var];
    for (const Variable &var : row_formula.GetFreeVariables()) {
      const int &theory_col = var_to_theory_col_.at(var.get_id());
      TheoryBoundsToBoundIdxs(theory_col, bounds_ray[theory_col], last_theory_rows_to_explanation_);
    }
  }

  DLINEAR_ASSERT(!last_theory_rows_to_explanation_.empty(), "explanation must contain at least a violation");
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::UpdateExplanationInfeasible: ↦ {}", last_theory_rows_to_explanation_);
}

void CompleteSoplexTheorySolver::UpdateExplanationStrictInfeasible() {
  DLINEAR_ASSERT(last_theory_rows_to_explanation_.empty(), "last explanation must be empty");

  // Solution vector. Contains the value of all the variables
  soplex::VectorRational x{spx_.numColsRational()};
  [[maybe_unused]] bool has_sol = spx_.getPrimalRational(x);
  DLINEAR_ASSERT(has_sol, "has_sol must be true");
  soplex::VectorRational dual{spx_.numRowsRational()};
  [[maybe_unused]] const bool has_dual = spx_.getDualRational(dual);
  DLINEAR_ASSERT(has_dual, "has_dual must be true");

  std::set<Variable> visited_variables;
  for (int i = 0; i < dual.dim(); ++i) {
    // Skip inactive rows
    if (dual[i].is_zero()) continue;
    last_theory_rows_to_explanation_.insert(i);
    const auto &row_formula = predicate_abstractor_[theory_row_to_lit_[i].var];
    for (const Variable &var : row_formula.GetFreeVariables()) visited_variables.insert(var);
  }

  DLINEAR_DEBUG_FMT("Strict active rows: {}", last_theory_rows_to_explanation_);

  // Run through the variables found in the active rows
  for (const Variable &var_id : visited_variables) {
    // Add all the bounds for the variable to explanation, if they are active
    const int theory_col = var_to_theory_col_.at(var_id.get_id());
    TheoryBoundsToBoundIdxs(theory_col, mpq_class{x[theory_col].backend().data()}, last_theory_rows_to_explanation_);
  }

  DLINEAR_ASSERT(!last_theory_rows_to_explanation_.empty(), "explanation must contain at least a violation");
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::UpdateExplanationStrictInfeasible: ↦ {}",
                    last_theory_rows_to_explanation_);
}

void CompleteSoplexTheorySolver::GetExplanation(Explanations &explanations) {
  DLINEAR_ASSERT(!theory_rows_to_explanations_.empty(), "there must be at least one explanation");
  DLINEAR_ASSERT(std::all_of(theory_rows_to_explanations_.begin(), theory_rows_to_explanations_.end(),
                             [](const std::set<int> &explanation) { return !explanation.empty(); }),
                 "no explanation can be empty");
  for (const std::set<int> &theory_rows_to_explanation : theory_rows_to_explanations_) {
    LiteralSet explanation;
    for (const int &theory_row : theory_rows_to_explanation) explanation.insert(theory_row_to_lit_[theory_row]);
    explanations.insert(explanation);
  }
  DLINEAR_ASSERT(explanations.size() == theory_rows_to_explanations_.size(), "explanations must have the same size");
}

std::set<size_t> CompleteSoplexTheorySolver::IteratorNqRowsInLastExplanation() const {
  std::set<size_t> nq_row_to_iterator_index;
  for (size_t i = 0; i < nq_row_to_theory_rows_.size(); i++) {
    const int &spx_row = nq_row_to_theory_rows_[i];
    if (last_theory_rows_to_explanation_.find(spx_row) != last_theory_rows_to_explanation_.end()) {
      nq_row_to_iterator_index.insert(i);
    }
  }
  return nq_row_to_iterator_index;
}

bool CompleteSoplexTheorySolver::UpdateBitIncrementIteratorBasedOnExplanation(BitIncrementIterator &bit_iterator) {
  // The last iteration yielded a feasible solution, but there were some other constraints that were violated before
  // Unlock the solver and go to the next iteration
  if (last_theory_rows_to_explanation_.empty()) {
    DLINEAR_ASSERT(locked_solver_, "The solver must have been locked before");
    locked_solver_ = false;
    if (single_nq_rows_.empty()) {
      ++bit_iterator;
    } else {
      for (const size_t &nq_row : single_nq_rows_) bit_iterator.Learn(nq_row);
      single_nq_rows_.clear();
    }
    EnableNqLiterals(*bit_iterator, true);
    // If we have an explanation to return, we can stop and return UNSAT
    return theory_rows_to_explanations_.empty();
  }

  const std::set<size_t> nq_in_explanation{IteratorNqRowsInLastExplanation()};
  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::CheckSat: nq_in_explanation = {}", nq_in_explanation);
  DLINEAR_ASSERT(!nq_in_explanation.empty(), "nq_in_explanation must not be empty");

  // Find and update the current explanation for this set of nq constraints
  auto it = nq_explanations_.find(nq_in_explanation);
  if (it == nq_explanations_.end()) {
    DLINEAR_TRACE("CompleteSoplexTheorySolver::CheckSat: explanation not seen yet. Adding to the set");
    it = nq_explanations_.emplace(nq_in_explanation, nq_in_explanation).first;
  }

  NqExplanation &nq_explanation = it->second;
  const size_t idx = bool_vector_to_int(*bit_iterator, nq_in_explanation);
  // If the same boolean combination of these non-equal rows has been tried before, we can skip it
  if (!nq_explanation.visited[idx]) {
    DLINEAR_TRACE("CompleteSoplexTheorySolver::CheckSat: new explanation. Adding the new explanation to the set");
    nq_explanation.visited[idx] = true;
    nq_explanation.explanation.insert(last_theory_rows_to_explanation_.cbegin(),
                                      last_theory_rows_to_explanation_.cend());

    if (nq_in_explanation.size() == 1) single_nq_rows_.insert(*nq_in_explanation.begin());

    // All boolean combinations of this set of non-equal rows have been tried, so the problem is UNSAT
    if (std::all_of(nq_explanation.visited.begin(), nq_explanation.visited.end(), [](bool b) { return b; })) {
      DLINEAR_DEBUG("CompleteSoplexTheorySolver::CheckSat: all combinations of nq_in_explanation tried. Infeasible");
      theory_rows_to_explanations_.insert(nq_explanation.explanation);
    }
  }

  // Remove the last infeasible constraints and try again, ensuring that the solver is locked
  DLINEAR_DEBUG("CompleteSoplexTheorySolver::CheckSat: removing last infeasible nq constraints and try again");
  DisableNqLiterals(nq_in_explanation);
  locked_solver_ = true;
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

void CompleteSoplexTheorySolver::EnableSpxRow(int spx_row, bool truth) {
  const LpRowSense sense = truth ? spx_sense_[spx_row] : !spx_sense_[spx_row];
  const mpq_class &rhs{spx_rhs_[spx_row]};
  soplex::LPRowRational lp_row;
  spx_.getRowRational(spx_row, lp_row);
  soplex::DSVectorRational row_vector{lp_row.rowVector()};
  // Remove the strict variable from the row and add it back with the right coefficient
  int strict_variable_pos = row_vector.pos(STRICT_VARIABLE_IDX);
  if (strict_variable_pos < 0) {
    row_vector.add(STRICT_VARIABLE_IDX, 1);
    strict_variable_pos = row_vector.pos(STRICT_VARIABLE_IDX);
  }
  switch (sense) {
    case LpRowSense::LT:
      row_vector.value(strict_variable_pos) = 1;
      break;
    case LpRowSense::GT:
      row_vector.value(strict_variable_pos) = -1;
      break;
    case LpRowSense::EQ:
    case LpRowSense::LE:
    case LpRowSense::GE:
      row_vector.value(strict_variable_pos) = 0;
      break;
    case LpRowSense::NQ:
      // No need to initialise the strict variable here since it will be enabled with all the nq rows
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

  theory_rows_state_.at(spx_row) = true;
  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::EnableLinearLiteral: Row({}) ↦ {} {} {} | Sense({})", spx_row,
                    lp_row.lhs(), lp_row.rowVector(), lp_row.rhs(), sense);
}

CompleteSoplexTheorySolver::NqExplanation::NqExplanation(size_t size) : explanation{}, visited(size, false) {}
CompleteSoplexTheorySolver::NqExplanation::NqExplanation(const std::set<size_t> &bits)
    : explanation{}, visited(1 << bits.size(), false) {}

}  // namespace dlinear
