/**
 * @file CompleteSoplexTheorySolver.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Complete version of SoplexTheorySolver.
 *
 * The LP solver used is Soplex.
 * This solver is complete. It means that it will always solve the linear problem exactly.
 */
#pragma once

#ifndef DLINEAR_ENABLED_SOPLEX
#error SoPlex is not enabled. Please enable it by adding "--//tools:enable_soplex" to the bazel command.
#endif

#include <map>
#include <optional>

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/SoplexTheorySolver.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/BitIncrementIterator.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"

namespace dlinear {

/**
 * CompleteSoPlexTheorySolver class.
 *
 * Complete solver using SoPlex.
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

  void AddLiteral(const Literal& lit) override;

  SatResult CheckSat(const Box& box, mpq_class* actual_precision, Explanations& explanations) override;

  void Reset(const Box& box) override;

 private:
  static const mpq_class strict_col_lb_;  ///< Zero. Used for the strict variable lower bound
  static const mpq_class strict_col_ub_;  ///< One. Used for the strict variable upper bound

  void EnableSPXVarBound() override;
  void EnableSpxRow(int spx_row, bool truth, const Variables& free_vars) override;

  /**
   * Internal method to check the satisfiability of the current LP problem.
   *
   * It invokes the LP solver and returns the result, as well as the actual precision of the solution, if any.
   * If the LP problem is infeasible (or strictly infeasible), it will also update the explanation
   * @ref theory_rows_to_explanation_.
   * @param actual_precision The actual precision of the solution, if any. Starts from the input, and is updated if the
   * LP solver returns a better precision
   * @return The result of the SAT check
   */
  SatResult SpxCheckSat(mpq_class* actual_precision);

  /**
   * Update the explanation with the current LP solution.
   *
   * A solution has been found, but a strict inequality has been violated.
   * The explanation must be updated using an artificial infeasibility core.
   */
  void UpdateExplanationStrictInfeasible();

  /** Update the explanation with the infeasible core. */
  void UpdateExplanationInfeasible();

  void Consolidate() override;

  /**
   * Get the index of the strict variable used to enforce the strict inequalities.
   * @return index of the strict variable
   */
  int strict_variable_idx() const;

  /**
   * Enable the non-equal constraints based on the current iterator value @p nq_status.
   *
   * Each element of @p nq_status is a boolean that indicates if the corresponding non-equal should be converted to a
   * @f$ < @f$ (if false) or @f$ > @f$ (if true) constraint.
   * If @p nq_status is empty (there are no not-equal constraints), this will do nothing.
   * @param nq_status The current state of the non-equal constraints
   */
  void EnableNqLiterals(const std::vector<bool>& nq_status);

  /**
   * Update the @ref BitIncrementIterator @p bit_iterator based on the current explanation.
   *
   * The @p bit_iterator is used to explore the sub-problems produced by considering the non-equal constraints.
   * It uses some heuristics to update the iterator based on the current explanation to skip redundant sub-problems.
   * There are two main cases, based on the number of non-equal rows in the explanation:
   * - If there are no non-equal rows, there is no point in visiting other sub-problems, since the infeasibility resides
   * in some other constraints, and the non-equal constraints are not relevant.
   * - It here is only 1 non-equal row and it is the first time this row appear alone, we know that the current
   * inequality violates some other constraints, so we can invert it immediately.
   * - If the same non-equal row appears alone again, we know that the current inequality is the one that is causing the
   * infeasibility, so we can stop and report the current explanation.
   * - If there are more than 1 non-equal row, we can't do anything, so we just leave the iterator as it is
   * @param bit_iterator The iterator used to explore the sub-problems to be updated
   * @return true if the loop should continue to enumerate the sub-problems
   * @return false if there is no point in continuing the loop and it can be stopped with the current explanation
   */
  bool UpdateBitIncrementIteratorBasedOnExplanation(BitIncrementIterator& bit_iterator);

  /**
   * Find the non-equal rows in the current explanation.
   * @return vector of the non-equal rows in the current explanation
   */
  std::vector<size_t> IteratorNqRowsInExplanation() const;

  /**
   * Add a new explanation to @p explanations from @ref theory_rows_to_explanation_.
   * @param[out] explanations the set of explanations to add the new explanation to
   */
  void GetExplanation(Explanations& explanations);
  /**
   * Get the explanation from @ref theory_rows_to_explanation_.
   * @param[out] explanation the explanation to be updated
   */
  void GetExplanation(LiteralSet& explanation);

  std::vector<int> enabled_strict_theory_rows_;                          ///< Vector of enabled strict theory rows
  std::map<Variable::Id, std::vector<int>> var_to_enabled_theory_rows_;  ///< variable id -> enabled theory row.
                                                                         ///< Does not include simple bounds
  std::vector<int> nq_row_to_theory_rows_;  ///< Index of row with a non-equal-to constraint in the order they appear
                                            ///< mapped to the corresponding spx_row
  std::vector<bool> last_nq_status_;        ///< Last status of the non-equal constraints.
                                            ///< Keeps track last sense of the constraints:
                                            ///< @f$ < @f$ (false) or @f$ > @f$ (true).

  std::set<int> theory_rows_to_explanation_;  ///< Set of theory rows that are part of the explanation
};

}  // namespace dlinear
