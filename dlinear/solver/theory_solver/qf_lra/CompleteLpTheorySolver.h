/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * CompleteLpTheorySolver class.
 */
#pragma once

#include "dlinear/solver/theory_solver/qf_lra/LpTheorySolver.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/BitIncrementIterator.h"

namespace dlinear {

class CompleteLpTheorySolver : public LpTheorySolver {
 public:
  explicit CompleteLpTheorySolver(const PredicateAbstractor& predicate_abstractor,
                                  const std::string& class_name = "CompleteLpTheorySolver");

  void AddLiteral(const Variable& formula_var, const Formula& formula) final;
  bool EnableLiteral(const Literal& lit, const ConflictCallback& conflict_cb) final;

  void Consolidate(const Box& model) final;
  void Backtrack() final;

  TheoryResult CheckSatCore(mpq_class* actual_precision, const ConflictCallback& conflict_cb) final;

 private:
  void EnableStrictRow(int row, bool truth);
  void EnableVarBound() final;
  void EnableNqLiterals(const std::vector<bool>& nq_status, bool force = false);
  void EnableNqLiteral(int row, bool truth);
  void DisableNqLiterals(const std::set<size_t>& nq_constraints);
  LpResult LpCheckSat();
  void UpdateRowExplanationInfeasible();
  void UpdateRowExplanationStrictInfeasible();
  std::set<size_t> IteratorNqRowsInLastExplanation() const;
  bool UpdateBitIncrementIteratorBasedOnExplanation(BitIncrementIterator& bit_iterator);
  void NotifyRowInfeasible(const ConflictCallback& conflict_cb);

  /**
   * Structure used to store the infeasibility explanation of a subset of non-equal constraints.
   */
  struct NqExplanation {
    explicit NqExplanation(std::size_t size);
    explicit NqExplanation(const std::set<std::size_t>& size);
    std::set<int> explanation;  ///< Indexes of a subset of non-equal constraints that are part of the explanation
    std::vector<bool> visited;  ///< Configuration of the non-equal constraints that have been visited
  };

  int strict_variable_idx_;  ///< Index of the strict variable in the LP solver

  std::vector<int> nq_row_to_theory_rows_;  ///< Index of row with a non-equal-to constraint in the order they appear
                                            ///< mapped to the corresponding spx_row
  std::vector<bool> last_nq_status_;        ///< Last status of the non-equal constraints.
                                            ///< Keeps track last sense of the constraints:
                                            ///< @f$ < @f$ (false) or @f$ > @f$ (true).

  std::set<int> last_infeasible_lp_rows_;                ///< Last set of theory rows that are part of the explanation
  std::set<std::set<int>> theory_rows_to_explanations_;  ///< Set that contains all the explanation the solver produced

  std::map<std::set<std::size_t>, NqExplanation> nq_explanations_;  ///< Map of non-equal explanations

  bool locked_solver_;  ///< Flag to indicate if the solver is locked. A locked solver will always return UNSAT.
  std::set<std::pair<std::size_t, bool>> single_nq_rows_;  ///< Set of non-equal rows that appear alone in the
                                                           ///< explanation, with the current assignment.
                                                           ///< Can be inverted at the next iteration
};

}  // namespace dlinear
