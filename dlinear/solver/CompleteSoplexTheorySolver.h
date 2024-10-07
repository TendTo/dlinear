/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Complete version of SoplexTheorySolver.
 *
 * The LP solver used is Soplex.
 * This solver is complete. It means that it will always solve the linear problem exactly.
 */
#pragma once

#ifndef DLINEAR_ENABLED_SOPLEX
#error SoPlex is not enabled. Please enable it by adding "--//tools:enable_soplex" to the bazel command.
#endif

#include <cstddef>
#include <map>
#include <set>
#include <string>
#include <vector>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/solver/SoplexTheorySolver.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/BitIncrementIterator.h"
#include "dlinear/util/Box.h"

namespace dlinear {

/**
 * Complete solver using SoPlex.
 * 
 * The linear is problem exactly, also dealing with strict inequalities.
 * As a tradeoff, the objective function is used internally, so it is not possible to maximise or minimise an
 * arbitrary expression.
 */
class CompleteSoplexTheorySolver : public SoplexTheorySolver {
 public:
  explicit CompleteSoplexTheorySolver(PredicateAbstractor& predicate_abstractor,
                                      const std::string& class_name = "CompleteSoplexTheorySolver");

  Explanations EnableLiteral(const Literal& lit) override;

  void AddVariable(const Variable& var) override;

  void AddLiteral(const Variable& formula_var, const Formula& formula) override;

  SatResult CheckSatCore(mpq_class* actual_precision, Explanations& explanations) override;

  void Reset() override;

 private:
  static const mpq_class strict_col_lb_;  ///< Zero. Used for the strict variable lower bound
  static const mpq_class strict_col_ub_;  ///< One. Used for the strict variable upper bound

  void EnableSpxVarBound() override;
  void EnableSpxRow(int spx_row, bool truth) override;

  /**
   * Internal method to check the satisfiability of the current LP problem.
   *
   * It invokes the LP solver and returns the result.
   * If the LP problem is infeasible (or strictly infeasible), it will also update the explanation.
   * @pre The expected precision must be 0.
   * @return The result of the SAT check
   * @see theory_rows_to_explanations_.
   */
  SatResult SpxCheckSat();

  /**
   * Update the explanation with the current LP solution.
   *
   * A solution has been found, but a strict inequality has been violated.
   * The explanation must be updated using an artificial infeasibility core.
   */
  void UpdateExplanationStrictInfeasible();

  /** Update the explanation with the infeasible core. */
  void UpdateExplanationInfeasible();

  void Consolidate(const Box& box) override;

  /**
   * Enable the non-equal constraint at row @p spx_row based on the given @p truth.
   *
   * The boolean value of @p truth indicates if the corresponding non-equal should be converted to
   * @f[
   * \begin{cases}
   * \text{lhs} < \text{rhs} & \text{if truth} = \text{false} \newline
   * \text{lhs} > \text{rhs} & \text{if truth} = \text{true}
   * \end{cases}
   * @f]
   * @param spx_row the row in the LP problem to be enabled
   * @param truth the sense of the non-equal constraint
   * @see EnableNqLiterals
   */
  void EnableNqLiteral(int spx_row, bool truth);
  /**
   * Enable the non-equal constraints based on the current iterator value @p nq_status.
   *
   * Each element of @p nq_status is a boolean that indicates if the corresponding non-equal should be converted to a
   * @f$ < @f$ (if false) or @f$ > @f$ (if true) constraint.
   * If @p nq_status is empty (there are no not-equal constraints), this will do nothing.
   * @note The indexes in @p nq_constraints will be converted back to the theory_rows using @ref nq_row_to_theory_rows_.
   * @warning Rows where the @ref last_nq_status_ is equal to the current @p nq_status will not be updated, unless
   * @p force is set to true.
   * @param nq_status the current state of the non-equal constraints
   * @see DisableNqLiterals
   */
  void EnableNqLiterals(const std::vector<bool>& nq_status, bool force = false);
  /**
   * Disable the non-equal constraints in the given set.
   *
   * Each element of @p nq_constraints is the index of the non-equal constraint that should be disabled.
   * The corresponding row in the LP problem will become a free row.
   * The effect can be undone by calling @ref EnableNqLiterals with `force = true`.
   * @note The indexes in @p nq_constraints will be converted back to the theory_rows using @ref nq_row_to_theory_rows_.
   * @param nq_constraints indexes of the non-equal constraints to be disabled
   * @see EnableNqLiterals
   */
  void DisableNqLiterals(const std::set<std::size_t>& nq_constraints);

  /**
   * Update the @ref BitIncrementIterator @p bit_iterator based on the current explanation.
   *
   * The @p bit_iterator is used to explore the sub-problems produced by considering the non-equal constraints.
   * It uses some heuristics to update the iterator based on the current explanation to skip redundant sub-problems.
   * Once an infeasibility is detected, the @ref IteratorNqRowsInLastExplanation method is used to determine which
   * non-equal constraints are part of the explanation.
   * If there is only one non-equal row responsible, the iterator learns to skip all future subproblems that contain
   * that row in the same configuration.
   * All the non-equal rows in the explanation are then temporarily disabled, to find any other infeasibilities,
   * repeating the process untill what remains is feasible.
   * The explanation collected this way are stored in the appropriate @ref nq_explanations_.
   * Configurations that have been visited before are immediately skipped.
   * If all possible configurations of a subset non-equal rows have been explored,
   * we can return immediately knowing the problem is infeasible.
   * @pre The subproblem without the non-equal constraints must be feasible.
   * @param bit_iterator the iterator used to explore the sub-problems to be updated
   * @return true if the loop should continue to enumerate the sub-problems
   * @return false if there is no point in continuing the loop and it can be stopped with the current explanation
   */
  bool UpdateBitIncrementIteratorBasedOnExplanation(BitIncrementIterator& bit_iterator);

  /**
   * Find the non-equal rows in the current explanation.
   * @return vector of the non-equal rows in the current explanation
   */
  std::set<std::size_t> IteratorNqRowsInLastExplanation() const;

  /**
   * Add a new explanation to @p explanations from @ref theory_rows_to_explanations_.
   * @param[out] explanations the set of explanations to add the new explanation to
   */
  void GetExplanation(Explanations& explanations);

  /**
   * Structure used to store the infeasibility explanation of a subset of non-equal constraints.
   */
  struct NqExplanation {
    explicit NqExplanation(std::size_t size);
    explicit NqExplanation(const std::set<std::size_t>& size);
    std::set<int> explanation;  ///< Indexes of a subset of non-equal constraints that are part of the explanation
    std::vector<bool> visited;  ///< Configuration of the non-equal constraints that have been visited
  };

  std::vector<int> nq_row_to_theory_rows_;  ///< Index of row with a non-equal-to constraint in the order they appear
                                            ///< mapped to the corresponding spx_row
  std::vector<bool> last_nq_status_;        ///< Last status of the non-equal constraints.
                                            ///< Keeps track last sense of the constraints:
                                            ///< @f$ < @f$ (false) or @f$ > @f$ (true).

  std::set<int> last_theory_rows_to_explanation_;        ///< Last set of theory rows that are part of the explanation
  std::set<std::set<int>> theory_rows_to_explanations_;  ///< Set that contains all the explanation the solver produced

  std::map<std::set<std::size_t>, NqExplanation> nq_explanations_;  ///< Map of non-equal explanations

  bool locked_solver_;  ///< Flag to indicate if the solver is locked. A locked solver will always return UNSAT.
  std::set<std::pair<std::size_t, bool>> single_nq_rows_;  ///< Set of non-equal rows that appear alone in the
                                                           ///< explanation, with the current assignment.
                                                           ///< Can be inverted at the next iteration
};

}  // namespace dlinear
