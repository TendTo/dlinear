/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "NNSoplexTheorySolver.h"

#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

using soplex::Rational;
using SoplexStatus = soplex::SPxSolver::Status;

NNSoplexTheorySolver::NNSoplexTheorySolver(PredicateAbstractor &predicate_abstractor, const std::string &class_name)
    : SoplexTheorySolver(predicate_abstractor, class_name),
      pl_theory_lit_{},
      enabled_pl_constraints_{},
      pl_explanations_{},
      soi_{0} {
  spx_.setIntParam(soplex::SoPlex::OBJSENSE, soplex::SoPlex::OBJSENSE_MINIMIZE);
}

void NNSoplexTheorySolver::SetPiecewiseLinearConstraints(
    const std::vector<std::unique_ptr<PiecewiseLinearConstraint>> &relu_constraints) {
  for (const auto &relu_constraint : relu_constraints) {
    pl_theory_lit_.emplace(relu_constraint->active_var(), relu_constraint.get());
    pl_theory_lit_.emplace(relu_constraint->inactive_var(), relu_constraint.get());
    // fmt::println("Adding relu constraint: {} - {}", relu_constraint->active_var(),
    // relu_constraint->inactive_var());
  }
}

void NNSoplexTheorySolver::AddLiteral(const Variable &formula_var, const Formula &formula) {
  DLINEAR_ASSERT(!is_consolidated_, "Cannot add literals after consolidation");
  // Literal is already present
  if (lit_to_theory_row_.contains(formula_var.get_id())) return;
  // Literal will be handled by the ReLU SOI
  // if (relu_theory_lit_.contains(formula_var)) return;
  DLINEAR_TRACE_FMT("NNSoplexTheorySolver::AddLiteral({})", formula);

  // Create the LP solver variables
  for (const Variable &var : formula.GetFreeVariables()) AddVariable(var);

  spx_sense_.emplace_back(~parseLpSense(formula));

  const int spx_row{spx_rows_.num()};

  const bool is_simple_bound = BoundPreprocessor::IsSimpleBound(formula);
  soplex::DSVectorRational coeffs{is_simple_bound ? soplex::DSVectorRational{} : ParseRowCoeff(formula)};
  if (is_simple_bound) spx_rhs_.emplace_back(0);
  spx_rows_.add(soplex::LPRowRational(-soplex::infinity, coeffs, soplex::infinity));
  if (2 == config_.simplex_sat_phase()) CreateArtificials(spx_row);

  // Update indexes
  lit_to_theory_row_.emplace(formula_var.get_id(), spx_row);
  theory_row_to_lit_.emplace_back(formula_var, true);

  DLINEAR_ASSERT(static_cast<std::size_t>(spx_row) == theory_row_to_lit_.size() - 1,
                 "incorrect theory_row_to_lit_.size()");
  DLINEAR_ASSERT(static_cast<std::size_t>(spx_row) == spx_sense_.size() - 1, "incorrect spx_sense_.size()");
  DLINEAR_ASSERT(static_cast<std::size_t>(spx_row) == spx_rhs_.size() - 1, "incorrect spx_rhs_.size()");
  DLINEAR_DEBUG_FMT("NNSoplexTheorySolver::AddLiteral: {} ↦ {}", formula, spx_row);
}

TheorySolver::Explanations NNSoplexTheorySolver::EnableLiteral(const Literal &lit) {
  DLINEAR_ASSERT(is_consolidated_, "The solver must be consolidate before enabling a literal");
  DLINEAR_ASSERT(predicate_abstractor_.var_to_formula_map().contains(lit.var), "var must map to a theory literal");

  const auto &[var, truth] = lit;
  DLINEAR_DEV_FMT("Enabled Literal {}", lit);

  // Literal will be handled by the ReLU SOI
  if (pl_theory_lit_.contains(var)) {
    const PiecewiseLinearConstraint &constraint = *pl_theory_lit_.at(var);
    // No point in adding both sides of the piecewise constraint. Just consider the true one
    if (!truth) return {};
    // fmt::println("Enabled ReLU literal: ({}) {} -> {}", constraint.fixed(), lit, constraint);
    // If the constraint is fixed, add it as a proper LP constraint.
    // Otherwise, use it to update the Sum of Infeasibility
    if (!constraint.fixed()) {
      const bool is_active = constraint.active_var().equal_to(var);
      enabled_pl_constraints_.emplace_back(&constraint, is_active, false);
      DLINEAR_DEV_FMT("ENABLED {} = fixed? {}\nIs active?: {}\n{}", lit, constraint.fixed(),
                      enabled_pl_constraints_.back().active, constraint);
      soi_ += is_active ? constraint.active_soi() : constraint.inactive_soi();
      return {};
    }
  }

  Explanations explanations{preprocessor_.EnableLiteral(lit)};
  if (!explanations.empty()) return explanations;

  const auto it = lit_to_theory_row_.find(var.get_id());
  // If the literal was not already among the constraints (rows) of the LP, it must be a learned literal.
  if (it == lit_to_theory_row_.end()) {
    DLINEAR_TRACE_FMT("NNSoplexTheorySolver::EnableLinearLiteral: ignoring ({}{})", truth ? "" : "¬", var);
    return {};
  }

  // A non-trivial linear literal from the input problem
  const int spx_row = it->second;
  // Update the truth value for the current iteration with the last SAT solver assignment
  theory_row_to_lit_[spx_row].truth = truth;

  DLINEAR_TRACE_FMT("NNSoplexTheorySolver::EnableLinearLiteral({})", lit);

  EnableSpxRow(spx_row, truth);
  // fmt::println("Enabled literal: {}", lit);
  return explanations;
}

SatResult NNSoplexTheorySolver::CheckSatCore(mpq_class *actual_precision, std::set<LiteralSet> &explanations) {
  // fmt::println("NN Soplex Theory Solver: SOI = {}", soi_);
  // Use the Sum of Infeasibility expression built so far to create the objective function of the optimization
  // with the goal of minimizing it
  SoiToObjFunction();
  // Set the bounds for the variables
  EnableSpxVarBound();
  // Remove all the disabled rows from the LP solver
  DisableSpxRows();

  // Now we call the solver
  DLINEAR_DEBUG_FMT("NNSoplexTheorySolver::CheckSat: calling SoPlex (phase {})", config_.simplex_sat_phase());

  // While the LP problem is not solved (either feasible with objective value <= precision or infeasible)
  while (true) {
    const std::size_t prev_size = explanations.size();

    // Try to solve the LP problem.
    switch (SpxCheckSat(actual_precision)) {
      case SpxCheckSatResult::SAT:  // A solution with the desired precision has been found
        UpdateModelSolution();
        DLINEAR_DEBUG("NNSoplexTheorySolver::CheckSat: returning sat");
        return SatResult::SAT_DELTA_SATISFIABLE;
      case SpxCheckSatResult::INFEASIBLE:  // The constraints are infeasible
        UpdateExplanations(explanations);
        DLINEAR_DEBUG("NNSoplexTheorySolver::CheckSat: returning unsat");
        return SatResult::SAT_UNSATISFIABLE;
      case SpxCheckSatResult::SOI_VIOLATION:  // The SOI constraint has been violated, invert a piecewise constraint
        // TODO(tend): temporary solution to avoid looping. Check if the explanation was added
        UpdateExplanationsWithCurrentPiecewiseLinearLiterals(explanations);
        // Tried all sub-problems, just return UNSAT and start over
        if (explanations.size() == prev_size || !InvertGreatestViolation()) {
          DLINEAR_DEBUG("NNSoplexTheorySolver::CheckSat: returning unsat");
          return SatResult::SAT_UNSATISFIABLE;
        }
        break;
      default:
        DLINEAR_UNREACHABLE();
    }
  }
}

NNSoplexTheorySolver::SpxCheckSatResult NNSoplexTheorySolver::SpxCheckSat(mpq_class *actual_precision) {
#if 0
  spx_.writeFile("/home/campus.ncl.ac.uk/c3054737/Programming/phd/dlinear/dump.lp");
#endif
  SoplexStatus status = spx_.optimize();
  Rational max_violation, sum_violation;

  // The status must be OPTIMAL, UNBOUNDED, or INFEASIBLE. Anything else is an error
  if (status != SoplexStatus::OPTIMAL && status != SoplexStatus::UNBOUNDED && status != SoplexStatus::INFEASIBLE) {
    DLINEAR_RUNTIME_ERROR_FMT("SoPlex returned {}. That's not allowed here", status);
  } else if (spx_.getRowViolationRational(max_violation, sum_violation)) {
    DLINEAR_DEBUG_FMT("DeltaSoplexTheorySolver::CheckSat: SoPlex returned {}, precision = {}", status, max_violation);
  } else {
    DLINEAR_DEBUG_FMT("NNSoplexTheorySolver::CheckSat: SoPlex has returned {}, but no precision", status);
  }

  // Add the precision (delta) to the expected violation
  const mpq_class violation_rhs{is_addition(soi_) ? -get_constant_in_addition(soi_) + *actual_precision
                                                  : *actual_precision};
  switch (status) {
    case SoplexStatus::OPTIMAL:
      fmt::println("Objective value: {}", gmp::to_mpq_class(spx_.objValueRational().backend().data()).get_d());
      return spx_.objValueRational() <= violation_rhs.get_mpq_t() ? SpxCheckSatResult::SAT
                                                                  : SpxCheckSatResult::SOI_VIOLATION;
    case SoplexStatus::INFEASIBLE:
      return SpxCheckSatResult::INFEASIBLE;
    default:
      DLINEAR_UNREACHABLE();
  }
}

bool NNSoplexTheorySolver::InvertGreatestViolation() {
  const int colcount = spx_.numColsRational();
  soplex::VectorRational x;
  x.reDim(colcount);
  [[maybe_unused]] const bool has_sol = spx_.getPrimalRational(x);
  DLINEAR_ASSERT(has_sol, "has_sol must be true");
  DLINEAR_ASSERT(x.dim() >= colcount, "x.dim() must be >= colcount");
  Environment env;
  for (int theory_col = 0; theory_col < static_cast<int>(theory_col_to_var_.size()); theory_col++) {
    const Variable &var{theory_col_to_var_[theory_col]};
    env[var] = gmp::to_mpq_class(x[theory_col].backend().data());
  }

  // fmt::println("x: {}", x);
  mpq_class max_cost{0};
  std::size_t max_cost_index{0};
  for (std::size_t i = 0; i < enabled_pl_constraints_.size(); i++) {
    const mpq_class cost{enabled_pl_constraints_[i].constraint->Cost(env, enabled_pl_constraints_[i].active)};
    // fmt::println("Cost of {}: {}", *enabled_pl_constraints_[i], cost.get_d());
    if (cost > max_cost) {
      max_cost = cost;
      max_cost_index = i;
    }
  }

  // fmt::println("Max cost {} belongs to constraint {}", max_cost,
  // *enabled_pl_constraints_[max_cost_index].constraint);
  DLINEAR_ASSERT(max_cost > 0, "max_cost must be > 0");

  const auto [constraint_ptr, active, fixed] = enabled_pl_constraints_[max_cost_index];

  if (fixed) {
    DLINEAR_ERROR("NNSoplexTheorySolver::InvertGreatestViolation: max cost belongs to a fixed constraint");
    return false;
  }
  enabled_pl_constraints_[max_cost_index].fixed = true;

  const PiecewiseLinearConstraint &constraint{*enabled_pl_constraints_[max_cost_index].constraint};
  // Update the Sum of Infeasibilities by removing the old soi cost and adding the new one
  soi_ += active ? -constraint.active_soi() + constraint.inactive_soi()
                 : -constraint.inactive_soi() + constraint.active_soi();

  enabled_pl_constraints_[max_cost_index].active = !active;

  // TODO(tend): this could be made more efficient by selectively changing the objective function coefficients
  SoiToObjFunction();
  // Related to issue
  spx_.clearBasis();
  return true;
}

void NNSoplexTheorySolver::UpdateExplanationsWithCurrentPiecewiseLinearLiterals(std::set<LiteralSet> &explanations) {
  LiteralSet explanation;
  for (const PlConstraint &enabled_pl_constraint : enabled_pl_constraints_) {
    explanation.emplace(enabled_pl_constraint.active ? enabled_pl_constraint.constraint->active_var()
                                                     : enabled_pl_constraint.constraint->inactive_var(),
                        true);
    DLINEAR_DEV_FMT("addidg {} to explanation", enabled_pl_constraint.active
                                                    ? enabled_pl_constraint.constraint->active_var()
                                                    : enabled_pl_constraint.constraint->inactive_var());
  }
  if (explanations.contains(explanation)) return;
  pl_explanations_.emplace(explanation);
  explanations.emplace(explanation);
}

void NNSoplexTheorySolver::SoiToObjFunction() {
  DLINEAR_DEBUG_FMT("NNSoplexTheorySolver::SoiToObjFunction: soi_ = {}", soi_);
  if (is_variable(soi_)) {
    for (std::size_t i = 0; i < theory_col_to_var_.size(); i++) {
      const Variable &var{theory_col_to_var_[i]};
      spx_.changeObjRational(static_cast<int>(i), var.equal_to(get_variable(soi_)) ? Rational(1) : Rational(0));
    }
  } else if (is_multiplication(soi_)) {
    for (std::size_t i = 0; i < theory_col_to_var_.size(); i++) {
      const Variable &var{theory_col_to_var_[i]};
      const auto it = get_base_to_exponent_map_in_multiplication(soi_).find(var);
      spx_.changeObjRational(static_cast<int>(i), it == get_base_to_exponent_map_in_multiplication(soi_).end()
                                                      ? Rational(0)
                                                      : Rational(get_constant_in_multiplication(soi_).get_mpq_t()));
    }
  } else if (is_addition(soi_)) {
    for (std::size_t i = 0; i < theory_col_to_var_.size(); i++) {
      const Variable &var{theory_col_to_var_[i]};
      const auto it = get_expr_to_coeff_map_in_addition(soi_).find(var);
      spx_.changeObjRational(static_cast<int>(i), it == get_expr_to_coeff_map_in_addition(soi_).end()
                                                      ? Rational(0)
                                                      : Rational(it->second.get_mpq_t()));
    }
  }
}

void NNSoplexTheorySolver::Reset() {
  SoplexTheorySolver::Reset();
  soi_ = 0;
  enabled_pl_constraints_.clear();
}

void NNSoplexTheorySolver::Consolidate(const Box &box) {
  if (is_consolidated_) return;
  enabled_pl_constraints_.reserve(pl_theory_lit_.size() / 2);
  SoplexTheorySolver::Consolidate(box);
}

void NNSoplexTheorySolver::EnableSpxRow(int spx_row, bool truth) {
  // Get the correct sense for the row, inverting it if the literals is false
  const LpRowSense sense = truth ? spx_sense_[spx_row] : -spx_sense_[spx_row];
  if (sense == LpRowSense::NQ) return;

  const mpq_class &rhs{spx_rhs_[spx_row]};
  spx_.changeRangeRational(
      spx_row,
      sense == LpRowSense::GE || sense == LpRowSense::EQ ? Rational(gmp::to_mpq_t(rhs)) : Rational(-soplex::infinity),
      sense == LpRowSense::LE || sense == LpRowSense::EQ ? Rational(gmp::to_mpq_t(rhs)) : Rational(soplex::infinity));
  theory_rows_state_.at(spx_row) = true;
  DLINEAR_ASSERT(truth == theory_row_to_lit_[spx_row].truth, "truth must be equal to stored lit truth");
  DLINEAR_TRACE_FMT("NNSoplexTheorySolver::EnableLinearLiteral({} {} {})", theory_row_to_lit_[spx_row], sense, rhs);
}
}  // namespace dlinear
