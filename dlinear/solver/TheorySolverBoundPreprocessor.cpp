/**
 * @file TheorySolverBoundPreprocessor.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "TheorySolverBoundPreprocessor.h"

#include <unordered_set>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/TheorySolver.h"

namespace dlinear {

TheorySolverBoundPreprocessor::TheorySolverBoundPreprocessor(const TheorySolver& theory_solver)
    : TheorySolverBoundPreprocessor{theory_solver.predicate_abstractor(), theory_solver.theory_col_to_var(),
                                    theory_solver.var_to_theory_col(), theory_solver.theory_row_to_lit(),
                                    theory_solver.theory_bounds()} {}
TheorySolverBoundPreprocessor::TheorySolverBoundPreprocessor(const PredicateAbstractor& predicate_abstractor,
                                                             const std::vector<Variable>& theory_col_to_var,
                                                             const std::map<Variable::Id, int>& var_to_theory_cols,
                                                             const std::vector<Literal>& theory_row_to_var,
                                                             const TheorySolverBoundVectorVector& theory_bounds)
    : config_{predicate_abstractor.config()},
      predicate_abstractor_{predicate_abstractor},
      theory_cols_{theory_col_to_var},
      var_to_cols_{var_to_theory_cols},
      theory_rows_{theory_row_to_var},
      theory_bounds_{theory_bounds} {}

bool TheorySolverBoundPreprocessor::AddConstraint(const int theory_row, const Formula& formula) {
  if (config_.disable_theory_preprocessor()) return false;
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::AddConstraint({}, {})", theory_row, formula);
  if (!ShouldPropagateBounds(formula)) return false;
  const BoundEdge edge = ExtractBoundEdge(theory_row, formula);
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::AddConstraint: from = {}, to = {}, weight = {}", std::get<0>(edge),
                    std::get<1>(edge), std::get<2>(edge));
  row_to_edges_.emplace(theory_row, edge);
  return true;
}

TheorySolverBoundPreprocessor::Explanations TheorySolverBoundPreprocessor::EnableConstraint(const int theory_row) {
  if (config_.disable_theory_preprocessor()) return {};
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::EnableConstraint({})", theory_row);
  // If the row was never added as an edge, skip
  const auto it = row_to_edges_.find(theory_row);
  if (it == row_to_edges_.end()) return {};
  // If the literal does not represent an equality relation, skip
  const auto& lit = theory_rows_.at(theory_row);
  if (!ShouldPropagateBounds(lit)) return {};
  // Add the edge to the bound_graph
  const auto& [from, to, weight] = row_to_edges_.at(theory_row);
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::EnableConstraint({}): adding {} --{}--> {} to bound_graph",
                    theory_row, from, weight, to);
  const bool conflicting_edge = bound_graph_.AddEdge(from, to, weight);
  // TODO: handle conflicting edges, such as x == y and x == 2y. Should kee track of these enforced zeros
  if (conflicting_edge) DLINEAR_RUNTIME_ERROR("Conflicting edge not yet implemented! Disable the preprocessor!");
  return {};
}

TheorySolverBoundPreprocessor::Explanations TheorySolverBoundPreprocessor::Process(
    const std::vector<int>& enabled_theory_rows) {
  Explanations explanations;
  Process(enabled_theory_rows, explanations);
  return explanations;
}
void TheorySolverBoundPreprocessor::Process(Explanations& explanations) {
  if (config_.disable_theory_preprocessor()) return;
  DLINEAR_TRACE("TheorySolverBoundPreprocessor::Process()");
  SetEnvironmentFromBounds();
  PropagateEnvironment(explanations);
  DLINEAR_DEBUG_FMT("TheorySolverBoundPreprocessor::Process:{} conflict found during propagation",
                    explanations.empty() ? " no" : "");
}
void TheorySolverBoundPreprocessor::Process(const std::vector<int>& enabled_theory_rows, Explanations& explanations) {
  if (config_.disable_theory_preprocessor()) return;
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::Process({})", enabled_theory_rows);
  Process(explanations);
  if (!explanations.empty()) return;
  PropagateRows(enabled_theory_rows);
  EvaluateFormulas(enabled_theory_rows, explanations);
  DLINEAR_DEBUG_FMT("TheorySolverBoundPreprocessor::Process:{} conflict found during evaluation",
                    explanations.empty() ? " no" : "");
}

void TheorySolverBoundPreprocessor::Clear() {
  env_ = Environment{};
  row_graph_.Clear();
  bound_graph_.ClearEdges();
}

void TheorySolverBoundPreprocessor::SetEnvironmentFromBounds() {
  DLINEAR_ASSERT(theory_bounds_.size() >= theory_cols_.size(), "The number of bounds must be >= the number of columns");
  for (size_t theory_col = 0; theory_col < theory_cols_.size(); theory_col++) {
    const TheorySolverBoundVector& bound = theory_bounds_[theory_col];
    const mpq_class* active_bound = bound.GetActiveEqualityBound();
    if (active_bound == nullptr) continue;
    const Variable& var = theory_cols_[theory_col];
    env_[var] = *active_bound;
  }
}

void TheorySolverBoundPreprocessor::PropagateEnvironment(Explanations& explanations) {
  DLINEAR_TRACE("TheorySolverBoundPreprocessor::PropagateEnvironment: start propagation");
  const std::vector<std::pair<Variable, mpq_class>> vars_in_env{env_.begin(), env_.end()};
  std::unordered_set<Variable> visited;
  visited.reserve(theory_cols_.size());
  for (const auto& start_it : vars_in_env) {
    const auto [start_var, start_value] = start_it;
    if (visited.count(start_var) > 0) continue;
    bound_graph_.BFS(start_var, [&](const Variable& from, const Variable& to, const Weight& c) {
      DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::PropagateEnvironment: from = {}, to = {}, w = {}", from, to, c);
      if (to.equal_to(from)) return VisitResult::CONTINUE;
      DLINEAR_ASSERT(env_.find(from) != env_.end(), "The variable must be in the environment");
      DLINEAR_ASSERT(c != 0, "The coefficient must be non-zero");
      visited.insert(to);
      const mpq_class new_to_value = env_[from] * c.numeric;
      auto to_it = env_.find(to);
      if (to_it == env_.end()) {
        DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::PropagateEnvironment: propagate {} = {}", to, new_to_value);
        env_[to] = new_to_value;
      } else if (to_it->second != new_to_value) {
        DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::PropagateEnvironment: conflict caused by {} => {} = {} != {}",
                          from, to, to_it->second, new_to_value);
        const TheorySolverBoundVector& start_bounds = theory_bounds_.at(var_to_cols_.at(start_it.first.get_id()));
        const TheorySolverBoundVector& to_bounds = theory_bounds_.at(var_to_cols_.at(to.get_id()));
        DLINEAR_ASSERT(start_bounds.GetActiveEqualityBound() != nullptr, "The starting variable must have an eq bound");
        DLINEAR_ASSERT(to_bounds.GetActiveEqualityBound() != nullptr, "The conflicting variable must have an eq bound");

        AddPathsToExplanations(start_it.first, to, start_bounds, to_bounds, explanations);
      }
      return VisitResult::CONTINUE;
    });
  }
}

void TheorySolverBoundPreprocessor::PropagateRows(const std::vector<int>& enabled_theory_rows) {
  DLINEAR_TRACE("TheorySolverBoundPreprocessor::PropagateRows()");
  bool continue_propagating;
  do {
    continue_propagating = false;
    for (const auto theory_row : enabled_theory_rows) {
      const Literal& lit = theory_rows_.at(theory_row);
      if (!ShouldPropagateRows(lit)) continue;
      continue_propagating = true;
      const Formula& formula = predicate_abstractor_[lit.var];
      DLINEAR_ASSERT(is_addition(get_lhs_expression(formula)), "lhs expression must be an addition");
      std::vector<Variable> dependencies;
      mpq_class rhs{get_constant_value(get_rhs_expression(formula))};
      mpq_class var_coeff{};
      Variable var_propagated{};
      for (const auto& [expr, coeff] : get_expr_to_coeff_map_in_addition(get_lhs_expression(formula))) {
        DLINEAR_ASSERT(is_variable(expr), "All expressions in lhs formula must be variables");
        const Variable& var = get_variable(expr);
        const auto it = env_.find(var);
        if (it != env_.cend()) {
          rhs -= it->second * coeff;
          dependencies.emplace_back(var);
        } else {
          var_propagated = var;
          var_coeff = coeff;
        }
      }
      DLINEAR_ASSERT(!var_propagated.is_dummy(), "There must be exactly a propagated variable");

      // Calculate the propagated value of the variable
      rhs /= var_coeff;
      // Add all the dependencies edges to the graph
      for (auto& to_var : dependencies) row_graph_.AddEdge(var_propagated, to_var, theory_row, false);
      env_[var_propagated] = rhs;
      DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::PropagateRows: {} = {} thanks to row {} and {}", var_propagated,
                        rhs, theory_row, dependencies);
    }
  } while (continue_propagating);
}

void TheorySolverBoundPreprocessor::EvaluateFormulas(const std::vector<int>& enabled_theory_rows,
                                                     Explanations& explanations) {
  DLINEAR_ASSERT(explanations.empty(), "The explanations vector must be empty");
  DLINEAR_TRACE("TheorySolverBoundPreprocessor::EvaluateFormulas()");
  for (const auto& theory_row : enabled_theory_rows) {
    const Literal& lit = theory_rows_.at(theory_row);
    if (!ShouldEvaluate(lit)) continue;
    const Formula& formula = predicate_abstractor_[lit.var];
    const bool satisfied = formula.Evaluate(env_) == lit.truth;
    if (!satisfied) {
      DLINEAR_DEBUG_FMT("TheorySolverBoundPreprocessor::EvaluateFormulas: {} => FAIL", lit);
      FormulaViolationExplanation(lit, formula, explanations);
    }
  }
}

void TheorySolverBoundPreprocessor::FormulaViolationExplanation(const Literal& lit, const Formula& formula,
                                                                Explanations& explanations) {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::FormulaViolationExplanation({})", formula);
  // TODO: produce more than just one explanation! Produce as many as possible!
  LiteralSet explanation;
  explanation.insert(lit);
  for (const auto& var : formula.GetFreeVariables()) {
    DLINEAR_ASSERT(env_.find(var) != env_.end(), "All free variables must be in the environment");
    GetExplanation(var, explanation);
  }
  explanations.insert(explanation);
}

bool TheorySolverBoundPreprocessor::ShouldEvaluate(const Literal& lit) const {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldEvaluate({})", lit);
  // We already have checked this kind of formula when propagating the environment
  // While it wouldn't be an issue to do it again, it's more efficient to just do a quick check
  if (ShouldPropagateBounds(lit)) return false;
  const auto& [var, truth] = lit;
  const Formula& formula = predicate_abstractor_[var];
  // No need to evaluate if there are no free variables
  if (formula.GetFreeVariables().empty()) return false;
  // TODO: no need to evaluate rows that have an equality bound already expressed
  // All free variables must be in the environment
  return std::all_of(formula.GetFreeVariables().begin(), formula.GetFreeVariables().end(),
                     [this](const Variable& v) { return env_.find(v) != env_.end(); });
}
bool TheorySolverBoundPreprocessor::ShouldEvaluate(const Formula& formula) const {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldEvaluate({})", formula);
  // We already have checked this kind of formula when propagating the environment
  // While it wouldn't be an issue to do it again, it's more efficient to just do a quick check
  if (ShouldPropagateBounds(formula)) return false;
  // No need to evaluate if there are no free variables
  if (formula.GetFreeVariables().empty()) return false;
  // TODO: no need to evaluate rows that have an equality bound already expressed
  // All free variables must be in the environment
  return std::all_of(formula.GetFreeVariables().begin(), formula.GetFreeVariables().end(),
                     [this](const Variable& v) { return env_.find(v) != env_.end(); });
}

bool TheorySolverBoundPreprocessor::ShouldPropagateBounds(const Literal& lit) const {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldPropagateBounds({})", lit);
  const auto& [var, truth] = lit;
  const Formula& formula = predicate_abstractor_[var];
  // There must be exactly two free variables and an equality relation between them
  if (truth && !is_equal_to(formula)) return false;
  if (!truth && !is_not_equal_to(formula)) return false;
  return ShouldPropagateBounds(formula);
}
bool TheorySolverBoundPreprocessor::ShouldPropagateBounds(const Formula& formula) const {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldPropagateBounds({})", formula);
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  // There must be exactly two free variables and an equality relation between them
  if (formula.GetFreeVariables().size() != 2) return false;
  if (!is_equal_to(formula) && !is_not_equal_to(formula)) return false;

  // The formula must be of the form 'ax == by', with a,b != 0
  const Expression& lhs = get_lhs_expression(formula);
  const Expression& rhs = get_rhs_expression(formula);
  if (!is_addition(lhs) || get_constant_value(rhs) != 0) return false;
  const auto& expr_to_coeff_map = to_addition(lhs)->get_expr_to_coeff_map();
  if (expr_to_coeff_map.size() != 2) return false;
  return is_variable(expr_to_coeff_map.cbegin()->first) && is_variable(std::next(expr_to_coeff_map.cbegin())->first) &&
         expr_to_coeff_map.cbegin()->second != 0 && std::next(expr_to_coeff_map.cbegin())->second != 0;
}

bool TheorySolverBoundPreprocessor::ShouldPropagateRows(const Literal& lit) {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldPropagateRows({})", lit);
  const auto& [var, truth] = lit;
  const Formula& formula = predicate_abstractor_[var];
  // There must be exactly two free variables and an equality relation between them
  if (truth && !is_equal_to(formula)) return false;
  if (!truth && !is_not_equal_to(formula)) return false;
  return ShouldPropagateRows(formula);
}
bool TheorySolverBoundPreprocessor::ShouldPropagateRows(const Formula& formula) {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldPropagateRows({})", formula);
  // There must be exactly two free variables and an equality relation between them
  if (!is_equal_to(formula) && !is_not_equal_to(formula)) return false;
  if (formula.GetFreeVariables().size() < 2) return false;
  DLINEAR_ASSERT(is_addition(get_lhs_expression(formula)), "lhs expression must be an addition");

  size_t missing_var_count{0};
  for (const auto& [expr, coeff] : get_expr_to_coeff_map_in_addition(get_lhs_expression(formula))) {
    DLINEAR_ASSERT(is_variable(expr), "All expressions in lhs formula must be variables");
    if (env_.find(get_variable(expr)) != env_.cend()) continue;
    if (++missing_var_count > 1) return false;
  }
  return missing_var_count == 1;
}

TheorySolverBoundPreprocessor::BoundEdge TheorySolverBoundPreprocessor::ExtractBoundEdge(int theory_row,
                                                                                         const Formula& formula) const {
  DLINEAR_ASSERT(is_equal_to(formula), "Formula should be an equality relation");
  DLINEAR_ASSERT(formula.GetFreeVariables().size() == 2, "Formula should have exactly two free variables");
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  const Expression& lhs = get_lhs_expression(formula);

  const std::map<Expression, mpq_class>& map = get_expr_to_coeff_map_in_addition(lhs);
  DLINEAR_ASSERT(map.size() == 2, "Expression should have exactly two variables");
  DLINEAR_ASSERT(get_constant_value(get_rhs_expression(formula)) == 0, "The right-hand side must be 0");

  return {get_variable(map.cbegin()->first),                                         // From vertex (variable)
          get_variable(std::next(map.cbegin())->first),                              // To vertex (variable)
          {-(std::next(map.cbegin())->second) / map.cbegin()->second, theory_row}};  // Weight (coefficient, row)
}

void TheorySolverBoundPreprocessor::AddPathsToExplanations(const Variable& from, const Variable& to,
                                                           TheorySolverBoundPreprocessor::Explanations& explanations) {
  const TheorySolverBoundVector& from_bounds = theory_bounds_.at(var_to_cols_.at(from.get_id()));
  const TheorySolverBoundVector& to_bounds = theory_bounds_.at(var_to_cols_.at(to.get_id()));
  AddPathsToExplanations(from, to, from_bounds, to_bounds, explanations);
}
void TheorySolverBoundPreprocessor::AddPathsToExplanations(const Variable& from, const Variable& to,
                                                           const TheorySolverBoundVector& from_bounds,
                                                           const TheorySolverBoundVector& to_bounds,
                                                           TheorySolverBoundPreprocessor::Explanations& explanations) {
  bound_graph_.AllPaths(from, to, [&](std::vector<Variable>& path) {
    LiteralSet explanation;
    // Insert start and end bounds to the explanation
    from_bounds.GetActiveExplanation(theory_rows_, explanation);
    to_bounds.GetActiveExplanation(theory_rows_, explanation);
    // Insert all rows from the edges in the path to the explanation
    for (size_t i = 1; i < path.size(); i++) {
      DLINEAR_ASSERT(bound_graph_.GetEdgeWeight(path[i - 1], path[i]) != nullptr, "Edge must exist");
      const int theory_row = bound_graph_.GetEdgeWeight(path[i - 1], path[i])->data;
      explanation.insert(theory_rows_[theory_row]);
    }
    explanations.insert(explanation);
    return VisitResult::CONTINUE;
  });
}
void TheorySolverBoundPreprocessor::AddPathToExplanation(const Variable& from, const Variable& to,
                                                         LiteralSet& explanation) {
  const TheorySolverBoundVector& from_bounds = theory_bounds_.at(var_to_cols_.at(from.get_id()));
  const TheorySolverBoundVector& to_bounds = theory_bounds_.at(var_to_cols_.at(to.get_id()));
  AddPathToExplanation(from, to, from_bounds, to_bounds, explanation);
}
void TheorySolverBoundPreprocessor::AddPathToExplanation(const Variable& from, const Variable& to,
                                                         const TheorySolverBoundVector& from_bounds,
                                                         const TheorySolverBoundVector& to_bounds,
                                                         LiteralSet& explanation) {
  bound_graph_.AllPaths(from, to, [&](std::vector<Variable>& path) {
    // Insert start and end bounds to the explanation
    from_bounds.GetActiveEqExplanation(theory_rows_, explanation);
    to_bounds.GetActiveEqExplanation(theory_rows_, explanation);
    // Insert all rows from the edges in the path to the explanation
    for (size_t i = 1; i < path.size(); i++) {
      DLINEAR_ASSERT(bound_graph_.GetEdgeWeight(path[i - 1], path[i]) != nullptr, "Edge must exist");
      const int theory_row = bound_graph_.GetEdgeWeight(path[i - 1], path[i])->data;
      explanation.insert(theory_rows_[theory_row]);
    }
    return VisitResult::STOP;
  });
}

void TheorySolverBoundPreprocessor::GetExplanation(const Variable& var, LiteralSet& explanation) {
  const TheorySolverBoundVector& bounds = theory_bounds_.at(var_to_cols_.at(var.get_id()));
  // If the variable has its bounds set directly by some literals, simply add them to the explanation
  if (bounds.GetActiveEqualityBound() != nullptr) {
    bounds.GetActiveExplanation(theory_rows_, explanation);
  } else if (row_graph_.HasEdges(var)) {  // the variable value was obtained through row propagation, explore the graph
    row_graph_.BFS(var, [&](const Variable& from, const Variable& to, const int& theory_row) {
      if (from.equal_to(to)) return VisitResult::CONTINUE;
      explanation.insert(theory_rows_[theory_row]);
      if (row_graph_.HasEdges(to)) return VisitResult::CONTINUE;
      GetExplanation(to, explanation);
      return VisitResult::SKIP;
    });
  } else {  // else we need to find the variable responsible for the bound propagation from the bound_graph
    bound_graph_.BFS(var, [&](const Variable& from, const Variable& to, const Weight&) {
      if (to.equal_to(from)) return VisitResult::CONTINUE;
      const TheorySolverBoundVector& to_bounds = theory_bounds_.at(var_to_cols_.at(to.get_id()));
      if (to_bounds.GetActiveEqualityBound() == nullptr) return VisitResult::CONTINUE;
      AddPathToExplanation(var, to, bounds, to_bounds, explanation);
      return VisitResult::STOP;
    });
  }
}

std::ostream& operator<<(std::ostream& os, const TheorySolverBoundPreprocessor& preprocessor) {
  return os << "TheorySolverBoundPreprocessor{"
            << "env_ = " << preprocessor.env() << ", "
            << "theory_cols_ = " << preprocessor.theory_cols() << ", "
            << "theory_rows_ = " << preprocessor.theory_rows() << ", "
            << "theory_bounds_ = " << preprocessor.theory_bounds() << ", "
            << "row_graph_ = " << preprocessor.row_graph() << ", "
            << "bound_graph_ = " << preprocessor.bound_graph() << "}";
}

}  // namespace dlinear
