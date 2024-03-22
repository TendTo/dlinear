/**
 * @file TheorySolverBoundPreprocessor.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief TheorySolverBoundPreprocessor class.
 *
 * This class uses some basic algebraic operations to preprocess the constraints
 * and identify violations before invoking the solver.
 * Namely, the bounds are propagated through the constraints.
 */
#pragma once

#include <map>
#include <set>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

#include "dlinear/solver/TheorySolverBoundVector.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/environment.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Graph.hpp"

namespace dlinear {

// Forward declaration
class TheorySolver;

class TheorySolverBoundPreprocessor {
 public:
  using Edge = std::tuple<Variable, Variable, mpq_class>;
  using Explanations = std::set<LiteralSet>;
  TheorySolverBoundPreprocessor(const Config& config, const PredicateAbstractor& predicate_abstractor,
                                const std::vector<Variable>& theory_cols,
                                const std::map<Variable::Id, int>& var_to_theory_cols,
                                const std::vector<Literal>& theory_rows,
                                const TheorySolverBoundVectorVector& theory_bounds);
  TheorySolverBoundPreprocessor(const Config& config, const TheorySolver& theory_solver);

  bool AddConstraint(int theory_row, const Formula& formula, const Expression& expr);
  bool AddConstraint(int theory_row, const Formula& formula);
  /**
   * Enable a previously added constraint, adding an edge to the graph in order to propagate the bound.
   * @pre The literal in @ref theory_rows_ must have been updated with the correct truth value.
   * @param theory_row The row index of the constraint to enable
   * @return ?
   */
  Explanations EnableConstraint(int theory_row);
  Explanations Process();
  void Process(Explanations& explanations);

  void Clear();

  [[nodiscard]] const Environment& GetEnvironment() const { return env_; }
  [[nodiscard]] const TheorySolverBoundVectorVector& theory_bounds() const { return theory_bounds_; }
  [[nodiscard]] const std::vector<Variable>& theory_cols() const { return theory_cols_; }
  [[nodiscard]] const std::map<Variable::Id, int>& var_to_cols() const { return var_to_cols_; }
  [[nodiscard]] const std::vector<Literal>& theory_rows() const { return theory_rows_; }
  [[nodiscard]] const PredicateAbstractor& predicate_abstractor() const { return predicate_abstractor_; }
  [[nodiscard]] const Graph<Variable, mpq_class>& graph() const { return graph_; }
  [[nodiscard]] const Environment& env() const { return env_; }
  [[nodiscard]] const std::unordered_map<int, Edge>& edges() const { return row_to_edges_; }

 protected:
  bool ShouldPropagate(const Literal& lit, bool check_expr = false) const;
  bool ShouldPropagate(const Formula& lit, bool check_expr = false) const;
  bool ShouldPropagate(const Expression& expr) const;

  bool ShouldEvaluate(const Literal& lit) const;
  bool ShouldEvaluate(const Formula& lit) const;
  bool ShouldEvaluate(const Expression& expr) const;
  void SetEnvironmentFromBounds();
  void PropagateEnvironment(Explanations& explanations);
  void EvaluateFormulas(Explanations& explanations);
  void FormulaViolationExplanation(const Formula& formula, Explanations& explanations);

  [[nodiscard]] inline Expression ExtractExpression(const Formula& formula) const {
    Expression expr{(get_lhs_expression(formula) - get_rhs_expression(formula))};
    if (needs_expansion_) expr = expr.Expand();
    DLINEAR_ASSERT(expr.EqualTo(expr.Expand()), "The expression must be expanded");
    return expr;
  }

  Edge ExtractEdge(const Formula& formula) const;
  Edge ExtractEdge(const Expression& expr) const;

 private:
  const bool enabled;
  const bool needs_expansion_;
  const PredicateAbstractor& predicate_abstractor_;
  const std::vector<Variable>& theory_cols_;
  const std::map<Variable::Id, int>& var_to_cols_;
  const std::vector<Literal>& theory_rows_;
  const TheorySolverBoundVectorVector& theory_bounds_;
  Environment env_;
  Graph<Variable, mpq_class> graph_;
  std::unordered_map<int, Edge> row_to_edges_;
  std::map<std::pair<Variable::Id, Variable::Id>, int> edges_to_row_;
};

std::ostream& operator<<(std::ostream& os, const TheorySolverBoundPreprocessor& preprocessor);

}  // namespace dlinear
