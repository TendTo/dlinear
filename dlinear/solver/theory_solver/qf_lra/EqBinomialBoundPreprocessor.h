/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * EqBinomialBoundPreprocessor class.
 */
#pragma once

#include <map>
#include <memory>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

#include "dlinear/solver/theory_solver/TheoryPreprocessor.h"
#include "dlinear/solver/theory_solver/qf_lra/BoundVector.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/environment.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Graph.hpp"

namespace dlinear {

// Forward declaration
class TheorySolver;

class EqBinomialBoundPreprocessor : public TheoryPreprocessor {
 public:
  /** Edge value in the dependency tracking graph */
  struct EdgeValue {
    const mpq_class* c_from;  ///< Coefficient of the 'from' variable
    const mpq_class* c_to;    ///< Coefficient of the 'to' variable
    const mpq_class* rhs;     ///< Right-hand side of the equation
    Literal lit;              ///< Literal that generated the edge
  };
  /** Edge in the dependency tracking graph */
  struct Edge {
    Variable from;    ///< Variable from which the edge starts
    Variable to;      ///< Variable to which the edge goes
    EdgeValue value;  ///< Value of the edge
  };
  /**
   * Construct a new Eq Binomial Bound Checker Preprocessor object using the @p theory_solver.
   * @param theory_solver theory solver that will use this preprocessor
   * @param var_bounds bounds over each real variable. Shared with other preprocessors
   * @param env environment containing the variable's values. Shared with other preprocessors
   * @param class_name name of the subclass of the theory preprocessor used
   */
  EqBinomialBoundPreprocessor(const TheorySolver& theory_solver, const std::shared_ptr<BoundVectorMap>& var_bounds,
                              const std::shared_ptr<Environment>& env,
                              const std::string& class_name = "EqBinomialBoundPreprocessor");

  [[nodiscard]] Config::ExecutionStep run_on_step() const final;

  bool EnableLiteral(const Literal& lit, const ConflictCallback& conflict_cb) final;
  bool ProcessCore(const ConflictCallback& conflict_cb) final;
  void Backtrack() final;

  /** @getter{bounds over each real variable, eq binomial bound checker preprocessor} */
  [[nodiscard]] const BoundVectorMap& var_bounds() const { return *var_bounds_; }
  /** @getter{dependency traking graph, eq binomial bound checker preprocessor} */
  [[nodiscard]] const Graph<Variable, EdgeValue>& graph() const { return graph_; }
  /** @getter{environment, eq binomial bound checker preprocessor} */
  [[nodiscard]] const Environment& env() const { return *env_; }

 protected:
  /**
   * Check if the @p lit should be propagated.
   *
   * A literal can be propagated if:
   * - It encodes an equality relation when taking into account the truth value
   * - It contains exactly two free variables with non-zero coefficients
   * @param lit lit to check
   * @return true if the literal should be propagated
   * @return false if the literal should not be propagated
   */
  [[nodiscard]] bool ShouldPropagateBounds(const Literal& lit) const;
  /**
   * Check if the @p formula should be propagated.
   *
   * A @p formula can be propagated if:
   * - It encodes an equality or not equal to relation
   * - It contains exactly two free variables with non-zero coefficients
   * @param formula formula to check
   * @return true if the formula should be propagated
   * @return false if the formula should not be propagated
   */
  [[nodiscard]] bool ShouldPropagateBounds(const Formula& formula) const;

  /**
   * Go through all the @ref var_bounds_ to set the @ref env_.
   *
   * Every time a variable has an active equality bound, the value is set in the environment @ref env_ .
   */
  void SetEnvironmentFromBounds();
  /**
   * Use the @p graph_ to propagate the bounds through the variables.
   *
   * Each node in the graph represents a variable, and each edge represents a dependency between two variables.
   * For example, the theory literal corresponding to the formula @f$ x + 4 y = 5 @f$ creates two directional edges
   * connecting the nodes @f$ x @f$ and @f$ y @f$.
   * Starting from all the nodes with an equality bound, the algorithm propagates the bounds through the graph.
   * There are three possible scenarios:
   * - **The destination node has not been assigned a value yet**: the value is set, a new equality bound is added and
   * the exploration continues
   * - **The destination node has a matching value**: the exploration skips all the edges from this node
   * - **The destination node has a different value**: a conflict is detected. An explanation is produced and the
   * exploration skips all the edges from this node
   *
   * @mermaid
   *  flowchart TD
   *  x((x))
   *  y((y))
   *  z((z))
   *  w((w))
   *  x <-- "2x + 3y = 2" --> y
   *  y <-- "-y + 5z = 0" --> z
   *  y <-- "y - 7w = -1" --> w
   * @endmermaid
   * @param conflict_cb callback to call when a conflict is detected. It will receive the explanation
   * @return true if no conflicts are detected at this step
   * @return false if a conflict is detected at this step
   */
  bool PropagateEnvironment(const ConflictCallback& conflict_cb);

  /**
   * Create an edge from the @p lit.
   * @param lit literal to extract the edge from
   * @return edge extracted from the literal. It will contain the from and to variables and the edge value
   */
  [[nodiscard]] Edge ExtractBoundEdge(const Literal& lit) const;

 private:
  std::shared_ptr<BoundVectorMap> var_bounds_;  ///< Bounds over each real variable. Shared with other preprocessors
  std::shared_ptr<Environment> env_;  ///< Environment containing the variable's values. Shared with other preprocessors
  Graph<Variable, EdgeValue> graph_;  ///< Dependency tracking graph
};

inline bool operator==(const EqBinomialBoundPreprocessor::EdgeValue& lhs,
                       const EqBinomialBoundPreprocessor::EdgeValue& rhs) {
  return lhs.c_from == rhs.c_from && lhs.c_to == rhs.c_to && lhs.rhs == rhs.rhs && lhs.lit == rhs.lit;
}

std::ostream& operator<<(std::ostream& os, const EqBinomialBoundPreprocessor& preprocessor);
std::ostream& operator<<(std::ostream& os, const EqBinomialBoundPreprocessor::EdgeValue& edge_value);
std::ostream& operator<<(std::ostream& os, const EqBinomialBoundPreprocessor::Edge& edge);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::EqBinomialBoundPreprocessor::EdgeValue)
OSTREAM_FORMATTER(dlinear::EqBinomialBoundPreprocessor::Edge)
OSTREAM_FORMATTER(dlinear::EqBinomialBoundPreprocessor)

#endif
