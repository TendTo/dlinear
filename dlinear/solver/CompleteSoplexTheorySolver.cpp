/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
// IWYU pragma: no_include <new>
#include "CompleteSoplexTheorySolver.h"

#include <algorithm>
#include <map>
#include <utility>

#include "dlinear/libs/libsoplex.h"
#include "dlinear/solver/LpColBound.h"
#include "dlinear/solver/LpRowSense.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

#define STRICT_VARIABLE_IDX (spx_.numColsRational() - 1)

namespace dlinear {

namespace {

inline std::size_t bool_vector_to_int(const std::vector<bool> &v, const std::set<std::size_t> &positions) {
  std::size_t result = 0;
  for (const std::size_t &pos : positions) {
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
  DLINEAR_ASSERT(config_.simplex_sat_phase() == 1, "CompleteSoplexTheorySolver must use phase 1");
}

void CompleteSoplexTheorySolver::AddVariable(const Variable &var) {
  auto it = var_to_theory_col_.find(var.get_id());
  // The variable is already present
  if (it != var_to_theory_col_.end()) return;
  SoplexTheorySolver::AddVariable(var);
}

void CompleteSoplexTheorySolver::AddLiteral(const Variable &formula_var, const Formula &formula) {
  DLINEAR_ASSERT(!is_consolidated_, "Cannot add literals after consolidation");
  // Literal is already present
  if (lit_to_theory_row_.contains(formula_var.get_id())) return;

  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::AddLiteral({})", formula);

  // Create the LP solver variables
  for (const Variable &var : formula.GetFreeVariables()) AddVariable(var);

  spx_sense_.emplace_back(parseLpSense(formula));

  const int spx_row{spx_rows_.num()};

  // Add an inactive constraint with the right coefficients for the decisional variables
  soplex::DSVectorRational coeffs{ParseRowCoeff(formula)};
  spx_rows_.add(soplex::LPRowRational(-soplex::infinity, coeffs, soplex::infinity));

  // Update indexes
  lit_to_theory_row_.emplace(formula_var.get_id(), spx_row);
  theory_row_to_lit_.emplace_back(formula_var, true);
  last_nq_status_.push_back(false);

  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == theory_row_to_lit_.size() - 1, "incorrect theory_row_to_lit_.size()");
  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == spx_sense_.size() - 1, "incorrect spx_sense_.size()");
  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == spx_rhs_.size() - 1, "incorrect spx_rhs_.size()");
  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == last_nq_status_.size() - 1, "incorrect spx_rhs_.size()");
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::AddLiteral: {} ↦ {}", formula_var, spx_row);
}

CompleteSoplexTheorySolver::Explanations CompleteSoplexTheorySolver::EnableLiteral(const Literal &lit) {
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");
  DLINEAR_ASSERT(predicate_abstractor_.var_to_formula_map().contains(lit.var), "var must map to a theory literal");

  Explanations explanations{preprocessor_.EnableLiteral(lit)};
  if (!explanations.empty()) return explanations;

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

  const Formula &formula = predicate_abstractor_[var];
  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::EnableLinearLiteral({})", lit);

  // If it is not a simple bound, we need to enable the row in the soplex solver
  // Later, active strict bounds will also appear in the LP problem as strict rows
  if (!BoundPreprocessor::IsSimpleBound(formula)) EnableSpxRow(spx_row, truth);
  return explanations;
}

SatResult CompleteSoplexTheorySolver::CheckSatCore(mpq_class *actual_precision, Explanations &explanations) {
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before checking for sat");

  // Set the bounds for the variables
  EnableSpxVarBound();
  // Remove all the disabled rows from the LP solver
  DisableSpxRows();

  // Now we call the solver
  DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: calling SoPlex (phase {})", config_.simplex_sat_phase());

  // First, check the sat result without taking into account nq constraints
  SatResult sat_status = SpxCheckSat();
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
  if (!it->empty()) DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::CheckSat: nq starting iterator = {}", it);

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
  switch (sat_status) {
    case SatResult::SAT_SATISFIABLE:
      UpdateModelSolution();
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
#if 0
  spx_.writeFile("/home/campus.ncl.ac.uk/c3054737/Programming/phd/dlinear/dump.lp");
#endif
  SoplexStatus status = spx_.optimize();
  Rational max_violation, sum_violation;

  // The status must be OPTIMAL, UNBOUNDED, or INFEASIBLE. Anything else is an error
  if (status != SoplexStatus::OPTIMAL && status != SoplexStatus::UNBOUNDED && status != SoplexStatus::INFEASIBLE) {
    DLINEAR_RUNTIME_ERROR_FMT("SoPlex returned {}. That's not allowed here", status);
  } else if (spx_.getRowViolationRational(max_violation, sum_violation)) {
    DLINEAR_ASSERT(max_violation.is_zero(), "max_violation must be 0");
    DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: SoPlex returned {}, precision = 0", status);
  } else {
    DLINEAR_DEBUG_FMT("CompleteSoplexTheorySolver::CheckSat: SoPlex has returned {}, but no precision", status);
  }

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
}

void CompleteSoplexTheorySolver::Reset() {
  SoplexTheorySolver::Reset();
  nq_row_to_theory_rows_.clear();
  theory_rows_to_explanations_.clear();
  nq_explanations_.clear();
  locked_solver_ = false;
  last_theory_rows_to_explanation_.clear();
  single_nq_rows_.clear();
}

void CompleteSoplexTheorySolver::Consolidate(const Box &box) {
  if (is_consolidated_) return;

  // Column of the strict auxiliary variable t bound between 0 and 1
  spx_cols_.add(soplex::LPColRational(1, soplex::DSVectorRational(), 1, 0));

  [[maybe_unused]] const auto rowcount = static_cast<size_t>(spx_rows_.num());
  [[maybe_unused]] const auto colcount = static_cast<size_t>(spx_cols_.num());
  DLINEAR_ASSERT_FMT(colcount == theory_col_to_var_.size() + 1, "incorrect theory_col_to_var_.size(): {} vs {}",
                     colcount, theory_col_to_var_.size());
  DLINEAR_ASSERT(colcount == var_to_theory_col_.size() + 1, "incorrect var_to_theory_col_.size()");
  DLINEAR_ASSERT(rowcount == spx_sense_.size(), "incorrect spx_sense_.size()");
  DLINEAR_ASSERT(rowcount == spx_rhs_.size(), "incorrect spx_rhs_.size()");
  DLINEAR_ASSERT(rowcount == last_nq_status_.size(), "incorrect spx_rhs_.size()");
  DLINEAR_ASSERT(rowcount == theory_row_to_lit_.size(), "incorrect theory_row_to_lit_.size()");
  DLINEAR_DEBUG("CompleteSoplexTheorySolver::Consolidate: consolidated");

  SoplexTheorySolver::Consolidate(box);
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
      BoundsToTheoryRows(var, bounds_ray[theory_col], last_theory_rows_to_explanation_);
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
    BoundsToTheoryRows(var_id, mpq_class{x[theory_col].backend().data()}, last_theory_rows_to_explanation_);
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
      for (const auto &[nq_row, nq_row_value] : single_nq_rows_) bit_iterator.Learn(nq_row, !nq_row_value);
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

    if (nq_in_explanation.size() == 1)
      single_nq_rows_.emplace(*nq_in_explanation.begin(), bit_iterator[*nq_in_explanation.begin()]);

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

void CompleteSoplexTheorySolver::EnableSpxVarBound() {
  SoplexTheorySolver::EnableSpxVarBound();
  // For all columns...
  for (const auto &[var, theory_bound] : preprocessor_.theory_bounds()) {
    // ... for each active bound of that column...
    for (BoundIterator it{theory_bound.GetActiveBound()}; it; ++it) {
      const auto &[value, bound, lit, expl] = *it;
      // ... if we are dealing with a strict bound, add the strict row to the LP problem
      if (bound == LpColBound::SU || bound == LpColBound::SL || bound == LpColBound::D) {
        SoplexTheorySolver::EnableSpxRow(lit_to_theory_row_.at(lit.var.get_id()));
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
  DLINEAR_TRACE_FMT("CompleteSoplexTheorySolver::EnableLinearLiteral: Row({}, {}) ↦ {} {} {} | Sense({})", spx_row,
                    theory_row_to_lit_[spx_row], lp_row.lhs(), lp_row.rowVector(), lp_row.rhs(), sense);
}

CompleteSoplexTheorySolver::NqExplanation::NqExplanation(size_t size) : explanation{}, visited(size, false) {}
CompleteSoplexTheorySolver::NqExplanation::NqExplanation(const std::set<size_t> &bits)
    : explanation{}, visited(1 << bits.size(), false) {}

}  // namespace dlinear
