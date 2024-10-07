/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * BoundImplicator class.
 *
 * This class is used to propagate some simple theory inferences in the SAT solver.
 * E.g.
 * @f[
 * x \le 10 \implies x < 4 \newline
 * x < 2 \implies \neg (x = 8)
 * @f]
 */
#pragma once

#include <compare>
#include <functional>
#include <map>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/LpRowSense.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/SortedVector.hpp"

namespace dlinear {

/**
 * Use theory reasoning to add relations between literals using some simple theory inferences.
 *
 * It will help the SAT solver to prune trivially unsatisfiable branches,
 * improving the chances of finding a feasible solution faster.
 * @pre All the assertions in the predicate_abstractor are flattered.
 */
class BoundImplicator {
 public:
  /**
   * Construct a BoundImplicator.
   * @param config configuration
   * @param assert assertion function. It adds assertions to the context
   * @param predicate_abstractor predicate abstractor containing the assertions
   */
  BoundImplicator(const Config& config, std::function<void(const Formula&)> assert,
                  const PredicateAbstractor& predicate_abstractor);

  /** Use theory reasoning to propagate some simple theory inferences. */
  void Propagate();

 private:
  /** Constraint. It is a tuple of value, row_sense and boolean variable */
  struct Constraint {
    mpq_class value;           ///< Value of the constraint
    LpRowSense row_sense;      ///< Type of the constraint (e.g. <=, <, =, >, >=)
    const Variable* variable;  ///< Boolean variable encoding the constraint

    std::strong_ordering operator<=>(const Constraint& o) const;
    bool operator==(const Constraint& o) const;
  };

  /**
   * Add an assertion to the @ref constraints_ map.
   *
   * Based on the number of free variables in the assertion, it will call the appropriate AddAssertion method.
   * @tparam NVariables number of free variables in the assertion
   * @param assertion assertion to add
   */
  template <int NVariables>
  void AddAssertion(const Formula& assertion);

  /**
   * Propagate the sorted constraints by adding them to the context by calling the @ref assert_ function.
   */
  void PropagateAssertions();

  const Config& config_;                                      ///< Configuration
  const std::function<void(const Formula&)> assert_;          ///< Assertion function. It adds assertions to the context
  const PredicateAbstractor& predicate_abstractor_;           ///< Predicate abstractor
  std::map<Variable, SortedVector<Constraint>> constraints_;  ///< Map of constraints for each variable
};

}  // namespace dlinear
