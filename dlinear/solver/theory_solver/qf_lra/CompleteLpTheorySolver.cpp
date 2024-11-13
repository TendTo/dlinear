/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "CompleteLpTheorySolver.h"

#include "dlinear/solver/theory_solver/qf_lra/BoundPreprocessor.h"
#include "dlinear/util/error.h"

namespace dlinear {

namespace {

inline std::size_t bool_vector_to_int(const std::vector<bool>& v, const std::set<std::size_t>& positions) {
  std::size_t result = 0;
  for (const std::size_t& pos : positions) {
    result <<= 1;
    result |= v.at(pos);
  }
  return result;
}

}  // namespace

CompleteLpTheorySolver::CompleteLpTheorySolver(const PredicateAbstractor& predicate_abstractor,
                                               const std::string& class_name)
    : LpTheorySolver{predicate_abstractor, class_name},
      nq_row_to_theory_rows_{},
      last_nq_status_{},
      last_infeasible_lp_rows_{},
      theory_rows_to_explanations_{},
      locked_solver_{false} {
  DLINEAR_ASSERT(config_.precision() == 0, "CompleteLpTheorySolver does not support a positive precision");
  DLINEAR_ASSERT(config_.simplex_sat_phase() == 1, "CompleteLpTheorySolver must use phase 1");
}

void CompleteLpTheorySolver::AddLiteral(const Variable& formula_var, const Formula& formula) {
  DLINEAR_ASSERT(!is_consolidated_, "Cannot add literals after consolidation");
  // Literal is already present
  if (lp_solver_->lit_to_row().contains(formula_var)) return;

  DLINEAR_TRACE_FMT("CompleteLpTheorySolver::AddLiteral({})", formula);

  // Create the LP solver variables
  for (const Variable& var : formula.GetFreeVariables()) AddVariable(var);

  lp_solver_->AddRow(formula_var, formula, parseLpSense(formula));
  last_nq_status_.push_back(false);

  DLINEAR_ASSERT(static_cast<size_t>(lp_solver_->num_rows()) == last_nq_status_.size(), "incorrect spx_rhs_.size()");
  DLINEAR_DEBUG_FMT("CompleteLpTheorySolver::AddLiteral: {} ↦ {}", formula, lp_solver_->num_rows());
}

bool CompleteLpTheorySolver::EnableLiteral(const Literal& lit, const ConflictCallback& conflict_cb) {
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");
  DLINEAR_ASSERT(pa_.var_to_formula_map().contains(lit.var), "var must map to a theory literal");
  // No need to enable a fixed literal again
  if (enabled_literals_checkpoint_.contains(lit.var)) return true;

  if (preprocessor_ != nullptr) {
    const bool success = preprocessor_->EnableLiteral(lit, conflict_cb);
    if (!success) return false;
  }

  const auto& [var, truth] = lit;
  const Formula& formula = pa_[var];
  const int row = lp_solver_->lit_to_row().at(var);

  // Go through the simple bounds to see if there is any trivially infeasible set of bounds
  if (BoundPreprocessor::IsSimpleBound(formula)) {
    DLINEAR_TRACE_FMT("CompleteLpTheorySolver::EnableLinearLiteral: enabling simple bound ({})", lit);
    const bool added = vars_bounds_.at(*formula.GetFreeVariables().cbegin())
                           .AddBound(BoundPreprocessor::GetSimpleBound(lit, formula), conflict_cb);
    if (!added) {
      DLINEAR_TRACE_FMT("CompleteLpTheorySolver::EnableLinearLiteral: failed to add simple bound ({})", lit);
      return false;
    }
  } else {
    // Since we know it is not a simple bounds, we can mark the row as active immediately
    rows_state_.at(row) = true;
    EnableStrictRow(row, truth);
  }

  // Update the truth value for the current iteration with the last SAT solver assignment
  lp_solver_->UpdateLiteralAssignment(row, truth);

  DLINEAR_TRACE_FMT("CompleteLpTheorySolver::EnableLinearLiteral({})", lit);
  return true;
}

void CompleteLpTheorySolver::EnableNqLiterals(const std::vector<bool>& nq_status, const bool force) {
  DLINEAR_TRACE_FMT("CompleteLpTheorySolver::EnableNqLiterals: nq_status = {}, force? = {}", nq_status, force);
  for (std::size_t i = 0; i < nq_status.size(); i++) {
    const int& row = nq_row_to_theory_rows_[i];
    // The row's sense has not changed since last time and the row is not in forced_nq_constraints, skip
    if (last_nq_status_[row] == nq_status[i] && !force) continue;
    EnableNqLiteral(row, nq_status[i]);
  }
}

void CompleteLpTheorySolver::EnableNqLiteral(const int row, const bool truth) {
  last_nq_status_[row] = truth;

  DLINEAR_DEBUG_FMT("CompleteLpTheorySolver::EnableNqLiterals: {} {} {}", lp_solver_->lit(row), (truth ? '>' : '<'),
                    lp_solver_->rhs().at(row));

  lp_solver_->SetCoefficient(row, strict_variable_idx_, truth ? -1 : 1);
  lp_solver_->EnableRow(row, truth ? LpRowSense::GE : LpRowSense::LE);
}

void CompleteLpTheorySolver::DisableNqLiterals(const std::set<size_t>& nq_constraints) {
  DLINEAR_TRACE_FMT("CompleteLpTheorySolver::DisableNqLiterals: nq_constraints = {}", nq_constraints);
  for (const size_t i : nq_constraints) {
    lp_solver_->DisableRow(nq_row_to_theory_rows_[i]);
  }
}

void CompleteLpTheorySolver::Consolidate(const Box& model) {
  if (is_consolidated_) return;

  strict_variable_idx_ = lp_solver_->num_columns();
  lp_solver_->AddColumn(1, 0, 1);

  DLINEAR_ASSERT_FMT(lp_solver_->num_rows() == static_cast<int>(last_nq_status_.size()),
                     "incorrect last_nq_status_ size: {} != {}", lp_solver_->num_rows(), last_nq_status_.size());

  LpTheorySolver::Consolidate(model);
}

TheoryResult CompleteLpTheorySolver::CheckSatCore(mpq_class* actual_precision, const ConflictCallback& conflict_cb) {
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before checking for sat");
  // This theory solver is complete, precision is always 0
  *actual_precision = 0;

  // Set the bounds for the variables
  EnableVarBound();

  // Remove all the disabled rows from the LP solver
  DisableNotEnabledRows();

  // Now we call the solver
  DLINEAR_DEBUG_FMT("CompleteLpTheorySolver::CheckSat: calling SoPlex (phase {})", config_.simplex_sat_phase());

  // First, check the sat result without taking into account nq constraints
  LpResult lp_result = LpCheckSat();
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: no nq constraints sat_status = {}", lp_result);
  if (lp_result == LpResult::ERROR) return TheoryResult::ERROR;
  if (lp_result == LpResult::INFEASIBLE) {
    theory_rows_to_explanations_.insert(last_infeasible_lp_rows_);
    NotifyRowInfeasible(conflict_cb);
    return TheoryResult::UNSAT;
  }

  // Initialise the iterator with the last nq statuses
  std::vector<bool> starting_iterator(nq_row_to_theory_rows_.size(), false);
  for (size_t i = 0; i < nq_row_to_theory_rows_.size(); i++) {
    starting_iterator[i] = last_nq_status_[nq_row_to_theory_rows_[i]];
  }
  BitIncrementIterator it(starting_iterator);
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: nq starting iterator size = {}", starting_iterator.size());
  if (!it->empty()) DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::CheckSat: nq starting iterator = {}", it);

  // Ensure that all non-equal constraints are enabled based on the current iterator value
  EnableNqLiterals(starting_iterator, true);
  // While there are nq constraints that are not satisfied, keep trying to solve the subproblems
  while (it) {
    // Clean up the last explanation
    last_infeasible_lp_rows_.clear();

    // Enable the non-equal constraints based on the current iterator value.
    // If the iterator is empty (there are no not-equal constraints), this will do nothing
    EnableNqLiterals(*it);

    // Omitting to do this seems to cause problems in soplex
    lp_solver_->Backtrack();

    // Solve the sub-problem
    lp_result = LpCheckSat();
    DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::CheckSat: intermediate lp_result = {}", lp_result);

    // If the problem is SAT and not locked, we can return immediately
    if (!locked_solver_ && (lp_result == LpResult::OPTIMAL || lp_result == LpResult::UNBOUNDED)) break;

    // Use some heuristics to update the iterator based on the current explanation.
    // Otherwise, just increment the iterator with the next configuration and try again
    if (!UpdateBitIncrementIteratorBasedOnExplanation(it)) break;
  }

  switch (lp_result) {
    case LpResult::OPTIMAL:
    case LpResult::UNBOUNDED:
      UpdateModelSolution();
      DLINEAR_DEBUG("CompleteLpTheorySolver::CheckSat: returning SAT");
      return TheoryResult::SAT;
    case LpResult::INFEASIBLE:
      NotifyRowInfeasible(conflict_cb);
      DLINEAR_DEBUG("CompleteLpTheorySolver::CheckSat: returning UNSAT");
      return TheoryResult::UNSAT;
    case LpResult::ERROR:
      DLINEAR_ERROR("CompleteLpTheorySolver::CheckSat: returning ERROR");
      return TheoryResult::ERROR;
    default:
      DLINEAR_UNREACHABLE();
  }
}

LpResult CompleteLpTheorySolver::LpCheckSat() {
#if 0
  spx_.writeFile("/home/campus.ncl.ac.uk/c3054737/Programming/phd/dlinear/dump.lp");
#endif
  static mpq_class zero{0};
  const LpResult result = lp_solver_->Optimise(zero);
  DLINEAR_ASSERT_FMT(zero == 0, "The returned precision must be 0. Got {}", zero);

  switch (result) {
    case LpResult::OPTIMAL:
    case LpResult::UNBOUNDED:
      if (lp_solver_->solution().at(strict_variable_idx_) > 0)
        return result == LpResult::OPTIMAL ? LpResult::OPTIMAL : LpResult::UNBOUNDED;
      UpdateRowExplanationStrictInfeasible();
      return LpResult::INFEASIBLE;
    case LpResult::INFEASIBLE:
      UpdateRowExplanationInfeasible();
      return LpResult::INFEASIBLE;
    case LpResult::ERROR:
      return LpResult::ERROR;
    default:
      DLINEAR_UNREACHABLE();
  }
}

void CompleteLpTheorySolver::UpdateRowExplanationInfeasible() {
  DLINEAR_ASSERT(!lp_solver_->infeasible_rows().empty(), "infeasible_rows must be available");
  DLINEAR_ASSERT(last_infeasible_lp_rows_.empty(), "last explanation must be empty");

  DLINEAR_TRACE_FMT("CompleteLpTheorySolver::UpdateRowExplanationInfeasible: infeasible rows: {}",
                    lp_solver_->infeasible_rows());
  DLINEAR_TRACE_FMT("CompleteLpTheorySolver::UpdateRowExplanationInfeasible: infeasible bounds: {}",
                    lp_solver_->infeasible_bounds());

  // Add all rows in the infeasible row vector to the last row explanation
  for (int row : lp_solver_->infeasible_rows()) {
    last_infeasible_lp_rows_.insert(row);
  }

  DLINEAR_TRACE_FMT("CompleteLpTheorySolver::UpdateRowExplanationInfeasible: theory_rows_to_explanation rows: {}",
                    last_infeasible_lp_rows_);

  // Convert the infeasible bounds to the corresponding row and add them to the explanation
  for (const auto& [column, upper_bound] : lp_solver_->infeasible_bounds()) {
    if (column == strict_variable_idx_) continue;  // Skip strict variable, for it is just auxiliary
    const Variable& var = lp_solver_->var(column);
    // Get the bounds of the variable and the bound value that caused the infeasibility
    const BoundVector& var_bounds = vars_bounds_.at(var);
    const mpq_class& value = upper_bound ? var_bounds.active_upper_bound() : var_bounds.active_lower_bound();
    // Get the explanation for that bound value and add all the rows corresponding to the literals to the explanation
    for (auto it = var_bounds.GetActiveBound(value); it; ++it) {
      last_infeasible_lp_rows_.insert(lp_solver_->row(it->theory_literal));
      for (const Literal& exp : it->explanation) last_infeasible_lp_rows_.insert(lp_solver_->row(exp));
    }
  }

  DLINEAR_TRACE_FMT("CompleteLpTheorySolver::UpdateRowExplanationInfeasible: theory_rows_to_explanation bounds: {}",
                    last_infeasible_lp_rows_);
}

void CompleteLpTheorySolver::UpdateRowExplanationStrictInfeasible() {
  DLINEAR_ASSERT(last_infeasible_lp_rows_.empty(), "last explanation must be empty");

  // Solution vectors for both primal and dual_solution problems
  const std::vector<mpq_class>& solution = lp_solver_->solution();
  const std::vector<mpq_class>& dual_solution = lp_solver_->dual_solution();
  DLINEAR_ASSERT(!solution.empty(), "solution must contain all the variables");
  DLINEAR_ASSERT(!dual_solution.empty(), "dual_solution must contain all the rows");

  std::set<Variable> active_variables;
  for (int i = 0; i < static_cast<int>(dual_solution.size()); ++i) {
    // Skip inactive rows
    if (dual_solution[i] == 0) continue;
    last_infeasible_lp_rows_.insert(i);
    const Formula& row_formula = pa_[lp_solver_->lit(i).var];
    for (const Variable& var : row_formula.GetFreeVariables()) active_variables.insert(var);
  }

  DLINEAR_DEBUG_FMT("Strict active rows: {}", last_infeasible_lp_rows_);

  // Run through the variables found in the active rows
  for (const Variable& var : active_variables) {
    // Add all the bounds for the variable to explanation, if they are active
    const int column = lp_solver_->column(var);
    for (auto it = vars_bounds_.at(var).GetActiveBound(solution[column]); it; ++it) {
      last_infeasible_lp_rows_.insert(lp_solver_->row(it->theory_literal));
      for (const Literal& exp : it->explanation) last_infeasible_lp_rows_.insert(lp_solver_->row(exp));
    }
  }

  DLINEAR_ASSERT(!last_infeasible_lp_rows_.empty(), "explanation must contain at least a violation");
  DLINEAR_DEBUG_FMT("CompleteLpTheorySolver::UpdateExplanationStrictInfeasible: ↦ {}", last_infeasible_lp_rows_);
}

std::set<size_t> CompleteLpTheorySolver::IteratorNqRowsInLastExplanation() const {
  std::set<size_t> nq_row_to_iterator_index;
  for (size_t i = 0; i < nq_row_to_theory_rows_.size(); i++) {
    const int row = nq_row_to_theory_rows_[i];
    if (last_infeasible_lp_rows_.contains(row)) {
      nq_row_to_iterator_index.insert(i);
    }
  }
  return nq_row_to_iterator_index;
}

bool CompleteLpTheorySolver::UpdateBitIncrementIteratorBasedOnExplanation(BitIncrementIterator& bit_iterator) {
  // The last iteration yielded a feasible solution, but there were some other constraints that were violated before
  // Unlock the solver and go to the next iteration
  if (last_infeasible_lp_rows_.empty()) {
    DLINEAR_ASSERT(locked_solver_, "The solver must have been locked before");
    locked_solver_ = false;
    if (single_nq_rows_.empty()) {
      ++bit_iterator;
    } else {
      for (const auto& [nq_row, nq_row_value] : single_nq_rows_) bit_iterator.Learn(nq_row, !nq_row_value);
      single_nq_rows_.clear();
    }
    EnableNqLiterals(*bit_iterator, true);
    // If we have an explanation to return, we can stop and return UNSAT
    return theory_rows_to_explanations_.empty();
  }

  const std::set<size_t> nq_in_explanation{IteratorNqRowsInLastExplanation()};
  DLINEAR_TRACE_FMT("CompleteLpTheorySolver::CheckSat: nq_in_explanation = {}", nq_in_explanation);
  DLINEAR_ASSERT(!nq_in_explanation.empty(), "nq_in_explanation must not be empty");

  // Find and update the current explanation for this set of nq constraints
  auto it = nq_explanations_.find(nq_in_explanation);
  if (it == nq_explanations_.end()) {
    DLINEAR_TRACE("CompleteLpTheorySolver::CheckSat: explanation not seen yet. Adding to the set");
    it = nq_explanations_.emplace(nq_in_explanation, nq_in_explanation).first;
  }

  NqExplanation& nq_explanation = it->second;
  const size_t idx = bool_vector_to_int(*bit_iterator, nq_in_explanation);
  // If the same boolean combination of these non-equal rows has been tried before, we can skip it
  if (!nq_explanation.visited[idx]) {
    DLINEAR_TRACE("CompleteLpTheorySolver::CheckSat: new explanation. Adding the new explanation to the set");
    nq_explanation.visited[idx] = true;
    nq_explanation.explanation.insert(last_infeasible_lp_rows_.cbegin(), last_infeasible_lp_rows_.cend());

    if (nq_in_explanation.size() == 1)
      single_nq_rows_.emplace(*nq_in_explanation.begin(), bit_iterator[*nq_in_explanation.begin()]);

    // All boolean combinations of this set of non-equal rows have been tried, so the problem is UNSAT
    if (std::all_of(nq_explanation.visited.begin(), nq_explanation.visited.end(), [](bool b) { return b; })) {
      DLINEAR_DEBUG("CompleteLpTheorySolver::CheckSat: all combinations of nq_in_explanation tried. Infeasible");
      theory_rows_to_explanations_.insert(nq_explanation.explanation);
    }
  }

  // Remove the last infeasible constraints and try again, ensuring that the solver is locked
  DLINEAR_DEBUG("CompleteSoplexTheorySolver::CheckSat: removing last infeasible nq constraints and try again");
  DisableNqLiterals(nq_in_explanation);
  locked_solver_ = true;
  return theory_rows_to_explanations_.empty();
}

void CompleteLpTheorySolver::EnableVarBound() {
  LpTheorySolver::EnableVarBound();
  // For all columns...
  for (const auto& [var, bounds] : vars_bounds_) {
    // ... for each active bound of that column...
    for (BoundIterator it{bounds.GetActiveBound()}; it; ++it) {
      const auto& [value, bound, lit, expl] = *it;
      // ... if we are dealing with a strict bound, add the strict row to the LP problem and disable the bound
      if (bound == LpColBound::SU || bound == LpColBound::SL || bound == LpColBound::D) {
        EnableStrictRow(lp_solver_->lit_to_row().at(lit.var), lit.truth);
      }
    }
  }
}

void CompleteLpTheorySolver::EnableStrictRow(int row, bool truth) {
  const LpRowSense sense = truth ? lp_solver_->senses()[row] : !lp_solver_->senses()[row];
  switch (sense) {
    case LpRowSense::LT:
      lp_solver_->SetCoefficient(row, strict_variable_idx_, 1);
      break;
    case LpRowSense::GT:
      lp_solver_->SetCoefficient(row, strict_variable_idx_, -1);
      break;
    case LpRowSense::EQ:
    case LpRowSense::LE:
    case LpRowSense::GE:
      lp_solver_->SetCoefficient(row, strict_variable_idx_, 0);
      break;
    case LpRowSense::NQ:
      // No need to initialise the strict variable here since it will be enabled with all other nq rows
      nq_row_to_theory_rows_.emplace_back(row);
      lp_solver_->DisableRow(row);
      break;
    default:
      DLINEAR_UNREACHABLE();
  }

  // If the sense is not nq, enable the row immediately. nq rows will be enabled later
  if (sense != LpRowSense::NQ) lp_solver_->EnableRow(row, ~sense);
  rows_state_.at(row) = true;

  DLINEAR_TRACE_FMT("CompleteLpTheorySolver::EnableStrictRow: Row({}, {}) ↦ Sense({})", row,
                    Literal{lp_solver_->lit(row).var, truth}, sense);
}

void CompleteLpTheorySolver::CreateCheckpoint() {
  LpTheorySolver::CreateCheckpoint();
  nq_row_to_theory_rows_checkpoint_ = nq_row_to_theory_rows_;
  DLINEAR_DEBUG_FMT("CompleteLpTheorySolver::CreateCheckpoint: #nq_row_to_theory_rows = {}",
                    nq_row_to_theory_rows_.size());
  DLINEAR_TRACE_FMT("CompleteLpTheorySolver::CreateCheckpoint: nq_row_to_theory_rows = {}", nq_row_to_theory_rows_);
}

void CompleteLpTheorySolver::Backtrack() {
  LpTheorySolver::Backtrack();
  nq_row_to_theory_rows_ = nq_row_to_theory_rows_checkpoint_;
  theory_rows_to_explanations_.clear();
  nq_explanations_.clear();
  locked_solver_ = false;
  last_infeasible_lp_rows_.clear();
  single_nq_rows_.clear();
}

void CompleteLpTheorySolver::NotifyRowInfeasible(const dlinear::ConflictCallback& conflict_cb) {
  DLINEAR_ASSERT(!theory_rows_to_explanations_.empty(), "there must be at least one explanation");
  DLINEAR_ASSERT(std::all_of(theory_rows_to_explanations_.begin(), theory_rows_to_explanations_.end(),
                             [](const std::set<int>& explanation) { return !explanation.empty(); }),
                 "no explanation can be empty");
  for (const std::set<int>& theory_rows_to_explanation : theory_rows_to_explanations_) {
    LiteralSet explanation;
    for (const int& theory_row : theory_rows_to_explanation) explanation.insert(lp_solver_->lit(theory_row));
    conflict_cb(explanation);
  }
}

CompleteLpTheorySolver::NqExplanation::NqExplanation(size_t size) : explanation{}, visited(size, false) {}
CompleteLpTheorySolver::NqExplanation::NqExplanation(const std::set<size_t>& bits)
    : explanation{}, visited(1 << bits.size(), false) {}

}  // namespace dlinear