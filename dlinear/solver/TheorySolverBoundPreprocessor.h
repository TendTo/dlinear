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
#include "dlinear/util/NumericDataContainer.hpp"

namespace dlinear {

// Forward declaration
class TheorySolver;

class TheorySolverBoundPreprocessor {
 public:
  using Weight = NumericDataContainer<mpq_class, int>;
  using BoundEdge = std::tuple<Variable, Variable, Weight>;
  using Explanations = std::set<LiteralSet>;
  TheorySolverBoundPreprocessor(const TheorySolver& theory_solver);
  TheorySolverBoundPreprocessor(const Config::ConstSharedConfig& config,
                                const PredicateAbstractor& predicate_abstractor,
                                const std::vector<Variable>& theory_cols,
                                const std::map<Variable::Id, int>& var_to_theory_cols,
                                const std::vector<Literal>& theory_rows,
                                const TheorySolverBoundVectorVector& theory_bounds);

  bool AddConstraint(int theory_row, const Formula& formula);
  /**
   * Enable a previously added constraint, adding an edge to the graph in order to propagate the bound.
   * @pre The literal in @ref theory_rows_ must have been updated with the correct truth value.
   * @param theory_row The row index of the constraint to enable
   * @return ?
   */
  Explanations EnableConstraint(int theory_row);
  Explanations Process(const std::vector<int>& enabled_theory_rows = {});
  void Process(Explanations& explanations);
  void Process(const std::vector<int>& enabled_theory_rows, Explanations& explanations);

  void Clear();

  [[nodiscard]] const Config::ConstSharedConfig& config_ptr() const { return config_; }
  [[nodiscard]] const Config& config() const { return *config_; }
  [[nodiscard]] const TheorySolverBoundVectorVector& theory_bounds() const { return theory_bounds_; }
  [[nodiscard]] const std::vector<Variable>& theory_cols() const { return theory_cols_; }
  [[nodiscard]] const std::map<Variable::Id, int>& var_to_cols() const { return var_to_cols_; }
  [[nodiscard]] const std::vector<Literal>& theory_rows() const { return theory_rows_; }
  [[nodiscard]] const PredicateAbstractor& predicate_abstractor() const { return predicate_abstractor_; }
  [[nodiscard]] const Graph<Variable, Weight>& bound_graph() const { return bound_graph_; }
  [[nodiscard]] const Graph<Variable, int>& row_graph() const { return row_graph_; }
  [[nodiscard]] const Environment& env() const { return env_; }
  [[nodiscard]] const std::unordered_map<int, BoundEdge>& edges() const { return row_to_edges_; }

 protected:
  bool ShouldPropagateBounds(const Literal& lit) const;
  bool ShouldPropagateBounds(const Formula& formula) const;
  bool ShouldPropagateRows(const Literal& lit);
  bool ShouldPropagateRows(const Formula& formula);
  bool ShouldEvaluate(const Literal& lit) const;
  bool ShouldEvaluate(const Formula& formula) const;

  void SetEnvironmentFromBounds();
  void PropagateEnvironment(Explanations& explanations);
  void PropagateRows(const std::vector<int>& enabled_theory_rows);
  void EvaluateFormulas(const std::vector<int>& enabled_theory_rows, Explanations& explanations);
  void FormulaViolationExplanation(const Literal& lit, const Formula& formula, Explanations& explanations);
  void AddPathsToExplanations(const Variable& from, const Variable& to, Explanations& explanations);
  void AddPathsToExplanations(const Variable& from, const Variable& to, const TheorySolverBoundVector& from_bounds,
                              const TheorySolverBoundVector& to_bounds, Explanations& explanations);
  void AddPathToExplanation(const Variable& from, const Variable& to, LiteralSet& explanation);
  void AddPathToExplanation(const Variable& from, const Variable& to, const TheorySolverBoundVector& from_bounds,
                            const TheorySolverBoundVector& to_bounds, LiteralSet& explanation);

  BoundEdge ExtractBoundEdge(int theory_row, const Formula& formula) const;

  void GetExplanation(const Variable& var, LiteralSet& explanation);

 private:
  const Config::ConstSharedConfig config_;
  const PredicateAbstractor& predicate_abstractor_;
  const std::vector<Variable>& theory_cols_;
  const std::map<Variable::Id, int>& var_to_cols_;
  const std::vector<Literal>& theory_rows_;
  const TheorySolverBoundVectorVector& theory_bounds_;
  Environment env_;
  Graph<Variable, Weight> bound_graph_;
  Graph<Variable, int> row_graph_;
  std::unordered_map<int, BoundEdge> row_to_edges_;
};

std::ostream& operator<<(std::ostream& os, const TheorySolverBoundPreprocessor& preprocessor);

}  // namespace dlinear
