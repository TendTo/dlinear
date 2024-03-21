/**
 * @file TheorySolverBoundPreprocessor.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "TheorySolverBoundPreprocessor.h"

#include <optional>

#include "dlinear/solver/TheorySolver.h"
#include "dlinear/util/logging.h"

namespace dlinear {

TheorySolverBoundPreprocessor::TheorySolverBoundPreprocessor(const Config& config,
                                                             const PredicateAbstractor& predicate_abstractor,
                                                             const std::vector<Variable>& theory_col_to_var,
                                                             const std::map<Variable::Id, int>& var_to_theory_cols,
                                                             const std::vector<Literal>& theory_row_to_var,
                                                             const TheorySolverBoundVectorVector& theory_bounds)
    : enabled{true},
      needs_expansion_{config.format() == Config::Format::SMT2 || config.filename_extension() == "smt2"},
      predicate_abstractor_{predicate_abstractor},
      theory_cols_{theory_col_to_var},
      var_to_cols_{var_to_theory_cols},
      theory_rows_{theory_row_to_var},
      theory_bounds_{theory_bounds} {}

TheorySolverBoundPreprocessor::TheorySolverBoundPreprocessor(const Config& config, const TheorySolver& theory_solver)
    : enabled{true},
      needs_expansion_{config.format() == Config::Format::SMT2 || config.filename_extension() == "smt2"},
      predicate_abstractor_{theory_solver.predicate_abstractor()},
      theory_cols_{theory_solver.theory_col_to_var()},
      var_to_cols_{theory_solver.lit_to_theory_row()},
      theory_rows_{theory_solver.theory_row_to_lit()},
      theory_bounds_{theory_solver.theory_bounds()} {}

bool TheorySolverBoundPreprocessor::AddConstraint(const int theory_row, const Formula& formula) {
  return AddConstraint(theory_row, formula, ExtractExpression(formula));
}
bool TheorySolverBoundPreprocessor::AddConstraint(const int theory_row, const Formula& formula,
                                                  const Expression& expr) {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::AddConstraint({}, {}, {})", theory_row, formula, expr);
  if (!ShouldPropagate(formula) || !ShouldPropagate(expr)) return false;
  const auto [from, to, weight] = ExtractEdge(expr);
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::AddConstraint: from = {}, to = {}, weight = {}", from, to, weight);
  row_to_edges_.emplace(theory_row, std::make_tuple(from, to, weight));
  edges_to_row_.emplace(std::make_pair(from.get_id(), to.get_id()), theory_row);
  return true;
}

std::vector<LiteralSet> TheorySolverBoundPreprocessor::EnableConstraint(const int theory_row) {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::EnableConstraint({})", theory_row);
  // If the row was never added as an edge, skip
  const auto it = row_to_edges_.find(theory_row);
  if (it == row_to_edges_.end()) return {};
  // If the literal does not represent an equality relation, skip
  const auto& lit = theory_rows_.at(theory_row);
  if (!ShouldPropagate(lit)) return {};
  // Add the edge to the graph
  const auto& [from, to, weight] = row_to_edges_.at(theory_row);
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::EnableConstraint({}): adding {} --{}--> {} to graph", theory_row,
                    from, to, weight);
  const bool conflicting_edge = graph_.AddEdge(from, to, weight);
  // TODO: handle this case
  if (conflicting_edge) DLINEAR_RUNTIME_ERROR("Conflicting edge not yet implemented!");
  return {};
}

std::vector<LiteralSet> TheorySolverBoundPreprocessor::Process() {
  std::vector<LiteralSet> explanations;
  Process(explanations);
  return explanations;
}
void TheorySolverBoundPreprocessor::Process(std::vector<LiteralSet>& explanations) {
  DLINEAR_TRACE("TheorySolverBoundPreprocessor::Process()");
  DLINEAR_WARN_FMT("Start env_ = {}", env_);
  DLINEAR_WARN_FMT("Start graph_ = {}", graph_);
  SetEnvironmentFromBounds();
  PropagateEnvironment(explanations);
  DLINEAR_WARN_FMT("End: env_ = {}", env_);
  DLINEAR_WARN_FMT("End: graph_ = {}", graph_);
  DLINEAR_WARN_FMT("Explanation: expl = {}", explanations);
  if (!explanations.empty()) return;
  //  EvaluateFormulas(explanations);
}

void TheorySolverBoundPreprocessor::Clear() {
  env_ = Environment{};
  graph_.ClearEdges();
}

void TheorySolverBoundPreprocessor::SetEnvironmentFromBounds() {
  DLINEAR_ASSERT(theory_bounds_.size() == theory_cols_.size(), "The number of bounds must match the number of columns");
  for (size_t theory_col = 0; theory_col < theory_bounds_.size(); theory_col++) {
    const TheorySolverBoundVector& bound = theory_bounds_[theory_col];
    const mpq_class* active_bound = bound.GetActiveEqualityBound();
    if (active_bound == nullptr) continue;
    const Variable& var = theory_cols_[theory_col];
    env_[var] = *active_bound;
  }
}

void TheorySolverBoundPreprocessor::PropagateEnvironment(std::vector<LiteralSet>& explanations) {
  DLINEAR_ERROR("TheorySolverBoundPreprocessor::PropagateEnvironment: start propagation");
  std::unordered_set<Variable> visited;
  std::set<LiteralSet> explanations_set;
  visited.reserve(theory_cols_.size());
  for (const auto& start_it : env_) {
    const auto [start_var, start_value] = start_it;
    if (visited.count(start_var) > 0) continue;
    graph_.BFS(start_var, [&](const Variable& from, const Variable& to, const mpq_class& c) {
      DLINEAR_ERROR_FMT("TheorySolverBoundPreprocessor::PropagateEnvironment: from = {}, to = {}, w = {}", from, to, c);
      if (to.equal_to(from)) return VisitResult::CONTINUE;
      DLINEAR_ASSERT(env_.find(from) != env_.end(), "The variable must be in the environment");
      DLINEAR_ASSERT(c != 0, "The coefficient must be non-zero");
      visited.insert(to);
      const mpq_class new_to_value = env_[from] * c;
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

        graph_.AllPaths(start_it.first, to, [&](std::vector<Variable>& path) {
          LiteralSet explanation;
          // Insert start and end bounds to the explanation
          start_bounds.GetActiveExplanation(theory_rows_, explanation);
          to_bounds.GetActiveExplanation(theory_rows_, explanation);
          // Insert all rows from the edges in the path to the explanation
          for (size_t i = 1; i < path.size(); i++) {
            const auto forward_it = edges_to_row_.find({path[i - 1].get_id(), path[i].get_id()});
            if (forward_it == edges_to_row_.end()) {
              const int theory_row = edges_to_row_.at({path[i].get_id(), path[i - 1].get_id()});
              explanation.insert(theory_rows_[theory_row]);
            } else {
              explanation.insert(theory_rows_[forward_it->second]);
            }
          }
          explanations_set.insert(explanation);
          return VisitResult::CONTINUE;
        });
      }
      return VisitResult::CONTINUE;
    });
  }
  explanations.reserve(explanations.size() + explanations_set.size());
  explanations.insert(explanations.end(), explanations_set.begin(), explanations_set.end());
}

void TheorySolverBoundPreprocessor::EvaluateFormulas(std::vector<LiteralSet>& explanations) {
  DLINEAR_ASSERT(explanations.empty(), "The explanations vector must be empty");
  DLINEAR_TRACE("TheorySolverBoundPreprocessor::EvaluateFormulas()");
  for (const auto& lit : theory_rows_) {
    if (!ShouldEvaluate(lit)) continue;
    const Formula& formula = predicate_abstractor_.var_to_formula_map().at(lit.first);
    const bool satisfied = formula.Evaluate(env_);
    if (!satisfied) FormulaViolationExplanation(formula, explanations);
  }
}

void TheorySolverBoundPreprocessor::FormulaViolationExplanation(const Formula& formula,
                                                                std::vector<LiteralSet>& explanations) {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::FormulaViolationExplanation({})", formula);
  // TODO: produce explanation out of the violation
}

bool TheorySolverBoundPreprocessor::ShouldEvaluate(const Literal& lit) const {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldEvaluate({})", lit);
  const auto& [var, truth] = lit;
  const Formula& formula = predicate_abstractor_.var_to_formula_map().at(var);
  // No need to evaluate if there are no free variables or only one free variable
  if (formula.GetFreeVariables().size() <= 1) return false;
  // All free variables must be in the environment
  if (std::any_of(formula.GetFreeVariables().begin(), formula.GetFreeVariables().end(),
                  [this](const Variable& v) { return env_.find(v) == env_.end(); })) {
    return false;
  }
  // We already have checked this kind of formula when propagating the environment
  // It's not a problem if we do it again, so just stick with the very inexpensive check
  return ShouldPropagate(lit);
}
bool TheorySolverBoundPreprocessor::ShouldEvaluate(const Formula& formula) const {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldEvaluate({})", formula);
  // No need to evaluate if there are no free variables or only one free variable
  if (formula.GetFreeVariables().size() <= 1) return false;
  // All free variables must be in the environment
  if (std::any_of(formula.GetFreeVariables().begin(), formula.GetFreeVariables().end(),
                  [this](const Variable& v) { return env_.find(v) == env_.end(); })) {
    return false;
  }
  // We already have checked this kind of formula when propagating the environment
  // It's not a problem if we do it again, so just stick with the very inexpensive check
  return ShouldPropagate(formula);
}
bool TheorySolverBoundPreprocessor::ShouldEvaluate(const Expression& expr) const {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldEvaluate({})", expr);
  return !ShouldPropagate(expr);
}

bool TheorySolverBoundPreprocessor::ShouldPropagate(const Literal& lit, const bool check_expr) const {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldPropagate({})", lit);
  const auto& [var, truth] = lit;
  const Formula& formula = predicate_abstractor_.var_to_formula_map().at(var);
  // There must be exactly two free variables and an equality relation between them
  if (formula.GetFreeVariables().size() != 2) return false;
  if (truth && !is_equal_to(formula)) return false;
  if (!truth && !is_not_equal_to(formula)) return false;
  return !check_expr || ShouldPropagate(ExtractExpression(formula));
}
bool TheorySolverBoundPreprocessor::ShouldPropagate(const Formula& formula, const bool check_expr) const {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldPropagate({})", formula);
  // There must be exactly two free variables and an equality relation between them
  return formula.GetFreeVariables().size() == 2 && (is_equal_to(formula) || is_not_equal_to(formula)) &&
         (!check_expr || ShouldPropagate(ExtractExpression(formula)));
}
bool TheorySolverBoundPreprocessor::ShouldPropagate(const Expression& expr) const {
  DLINEAR_ASSERT(expr.EqualTo(expr.Expand()), "The expression must be expanded");
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldPropagate({})", expr);

  // The formula must be of the form 'ax == by', with a,b != 0
  if (!is_addition(expr) || get_constant_in_addition(expr) != 0) return false;
  const auto& expr_to_coeff_map = to_addition(expr)->get_expr_to_coeff_map();
  if (expr_to_coeff_map.size() != 2) return false;
  return is_variable(expr_to_coeff_map.cbegin()->first) && is_variable(std::next(expr_to_coeff_map.cbegin())->first) &&
         expr_to_coeff_map.cbegin()->second != 0 && std::next(expr_to_coeff_map.cbegin())->second != 0;
}

TheorySolverBoundPreprocessor::Edge TheorySolverBoundPreprocessor::ExtractEdge(const Formula& formula) const {
  DLINEAR_ASSERT(is_equal_to(formula), "Formula should be an equality relation");
  DLINEAR_ASSERT(formula.GetFreeVariables().size() == 2, "Formula should have exactly two free variables");
  Expression expr{ExtractExpression(formula)};
  return ExtractEdge(expr);
}
TheorySolverBoundPreprocessor::Edge TheorySolverBoundPreprocessor::ExtractEdge(const Expression& expr) const {
  DLINEAR_ASSERT(ShouldPropagate(expr), "Expression must be propagable");
  DLINEAR_ASSERT(get_constant_in_addition(expr) == 0, "No constants must be present");

  const std::map<Expression, mpq_class>& map = get_expr_to_coeff_map_in_addition(expr);
  DLINEAR_ASSERT(map.size() == 2, "Expression should have exactly two variables");
  // Create a tuple containing the two variables and the coefficient between them
  // e.g. Expression{ax - by} -> std::tuple{x, y, -(-b)/a}
  return {get_variable(map.cbegin()->first), get_variable(std::next(map.cbegin())->first),
          -(std::next(map.cbegin())->second) / map.cbegin()->second};
}

std::ostream& operator<<(std::ostream& os, const std::vector<const Literal*>& theory_bounds) {
  for (const auto& bound : theory_bounds) os << *bound << " ";
  return os;
}

std::ostream& operator<<(std::ostream& os, const std::vector<Variable>& theory_bounds) {
  for (const auto& bound : theory_bounds) os << bound << " ";
  return os;
}

std::ostream& operator<<(std::ostream& os, const std::vector<Literal>& theory_bounds) {
  for (const auto& bound : theory_bounds) os << bound << " ";
  return os;
}

std::ostream& operator<<(std::ostream& os, const TheorySolverBoundPreprocessor& preprocessor) {
  os << "TheorySolverBoundPreprocessor{";
  os << "env_ = " << preprocessor.env() << ", ";
  os << "theory_cols_ = " << preprocessor.theory_cols() << ", ";
  os << "theory_rows_ = " << preprocessor.theory_rows() << ", ";
  os << "theory_bounds_ = " << preprocessor.theory_bounds() << ", ";
  os << "graph_ = " << preprocessor.graph();
  os << "}";
  return os;
}

}  // namespace dlinear
