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

#include <iosfwd>
#include <list>
#include <map>
#include <set>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/TheorySolverBoundVector.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/environment.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Graph.hpp"
#include "dlinear/util/logging.h"

namespace dlinear {
// Forward declaration
class TheorySolver;
}  // namespace dlinear

namespace dlinear {

class TheorySolverBoundPreprocessor {
 public:
  using Weight = int;
  using BoundEdge = std::tuple<Variable, Variable, Weight>;
  using Explanations = std::set<LiteralSet>;
  using RowToEqBinomialMap = std::unordered_map<int, mpq_class>;

  explicit TheorySolverBoundPreprocessor(const TheorySolver& theory_solver);
  TheorySolverBoundPreprocessor(const PredicateAbstractor& predicate_abstractor,
                                const std::vector<Variable>& theory_cols,
                                const std::map<Variable::Id, int>& var_to_theory_cols,
                                const std::vector<Literal>& theory_rows,
                                const TheorySolverBoundVectorVector& theory_bounds);

  bool AddConstraint(int theory_row, const Formula& formula);

  Explanations Process(const std::vector<int>& enabled_theory_rows = {});
  void Process(const std::vector<int>& enabled_theory_rows, Explanations& explanations);

  void GetActiveExplanation(int theory_col, LiteralSet& explanation);
  void GetActiveBoundIdxs(int theory_col, std::set<int>& bound_idxs);

  void Clear();

  [[nodiscard]] const Config& config() const { return config_; }
  [[nodiscard]] const TheorySolverBoundVectorVector& theory_bounds() const { return theory_bounds_; }
  [[nodiscard]] const std::vector<Variable>& theory_cols() const { return theory_cols_; }
  [[nodiscard]] const std::map<Variable::Id, int>& var_to_cols() const { return var_to_cols_; }
  [[nodiscard]] const std::vector<Literal>& theory_rows() const { return theory_rows_; }
  [[nodiscard]] const PredicateAbstractor& predicate_abstractor() const { return predicate_abstractor_; }
  [[nodiscard]] const Graph<Variable, Weight>& bound_graph() const { return graph_; }
  [[nodiscard]] const Environment& env() const { return env_; }
  [[nodiscard]] const RowToEqBinomialMap& edges() const { return row_to_eq_binomial_edge_coefficients_; }

 protected:
  enum class PropagateEqBinomialResult { NO_PROPAGATION, UNCHANGED, PROPAGATED, CONFLICT };

  bool ShouldPropagateEqBinomial(const Literal& lit) const;
  bool ShouldPropagateEqBinomial(const Formula& formula) const;
  bool ShouldPropagateRows(const Literal& lit);
  bool ShouldPropagateRows(const Formula& formula);
  bool ShouldEvaluate(const Literal& lit) const;
  bool ShouldEvaluate(const Formula& formula) const;

  void SetEnvironmentFromBounds();
  /**
   * Propagate the bounds of the variables in the given formula.
   *
   * It only works for formulas of the form @f$ ax = by @f$.
   * At least one of the two variables in the formula must have a value assigned in the @ref env_ .
   * Its value will be used to assign the value to the other variable, and a dependency edge will be added to the graph.
   * If the new assignment is incompatible with the current one, a conflict is found.
   * @pre the formula is of the form @f$ ax = by @f$.
   * @pre the formula has been added to @ref row_to_eq_binomial_edge_coefficients_ .
   * @param theory_row index of the theory row of the formula being propagated
   * @param explanations the explanations to be updated if a conflict is found
   * @return true if the propagation took place or a conflict has been found
   * @return false if no propagation took place. Both variables had no value assigned in the @ref env_ .
   */
  PropagateEqBinomialResult PropagateEqBinomial(int theory_row, Explanations& explanations);
  void PropagateConstraints(std::list<int>& enabled_theory_rows, Explanations& explanations);
  void EvaluateFormulas(std::list<int>& enabled_theory_rows, Explanations& explanations);
  void FormulaViolationExplanation(const Literal& lit, const Formula& formula, Explanations& explanations);
  void AddPathsToExplanations(const Variable& from, const Variable& to, const Literal& conflicting_literal,
                              Explanations& explanations);
  void AddPathsToExplanations(const Variable& from, const Variable& to, const TheorySolverBoundVector& from_bounds,
                              const TheorySolverBoundVector& to_bounds, Explanations& explanations);
  void AddPathToExplanation(const Variable& from, const Variable& to, LiteralSet& explanation);
  void AddPathToExplanation(const Variable& from, const Variable& to, const TheorySolverBoundVector& from_bounds,
                            const TheorySolverBoundVector& to_bounds, LiteralSet& explanation);
  void AddPathToExplanationBoundIdxs(const Variable& from, const Variable& to,
                                     const TheorySolverBoundVector& from_bounds,
                                     const TheorySolverBoundVector& to_bounds, std::set<int>& explanation);

  std::pair<Variable, Variable> ExtractBoundEdge(const Formula& formula) const;
  /**
   * Given a formula of the form @f$ ax = by @f$, with @f$ a, b \in \mathbb{R} @f$ being constants,
   * extract the coefficient @f$ c \coloneqq cx = y @f$.
   *
   * Variables enjoy total ordering between them.
   * The leftmost variable is always the smallest.
   * @param formula the formula to extract the coefficient from
   * @return the coefficient @f$ c @f$
   */
  mpq_class ExtractEqBoundCoefficient(const Formula& formula) const;

  void GetExplanation(const Variable& var, LiteralSet& explanation);
  void GetExplanationBoundIdxs(const Variable& var, std::set<int>& bound_idxs);

#if DEBUGGING_PREPROCESSOR
  std::vector<Variable> GetExplanationOrigins(const Variable& var);
#endif

 private:
  const Config& config_;
  const PredicateAbstractor& predicate_abstractor_;
  const std::vector<Variable>& theory_cols_;
  const std::map<Variable::Id, int>& var_to_cols_;
  const std::vector<Literal>& theory_rows_;
  const TheorySolverBoundVectorVector& theory_bounds_;
  Environment env_;
  Graph<Variable, Weight> graph_;
  RowToEqBinomialMap row_to_eq_binomial_edge_coefficients_;
};

std::ostream& operator<<(std::ostream& os, const TheorySolverBoundPreprocessor& preprocessor);

}  // namespace dlinear

OSTREAM_FORMATTER(dlinear::TheorySolverBoundPreprocessor)
