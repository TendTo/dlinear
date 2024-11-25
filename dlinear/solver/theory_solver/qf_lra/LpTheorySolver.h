/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * LpTheorySolver class.
 */
#pragma once

#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/theory_solver/qf_lra/LpSolver.h"
#include "dlinear/solver/theory_solver/qf_lra/QfLraTheorySolver.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"

namespace dlinear {

/**
 * Ensure the theory literals are consistent using a standard exact LP solver.
 */
class LpTheorySolver : public QfLraTheorySolver {
 public:
  explicit LpTheorySolver(const PredicateAbstractor& predicate_abstractor,
                          const std::string& class_name = "LpTheorySolver");

  void AddLiterals() final;
  void AddLiterals(std::span<const Literal> literals) override;

  void AddVariable(const Variable& var) override;
  void Consolidate(const Box& box) override;
  void Backtrack() override;

  /** @getter{LP solver, LpTheorySolver} */
  [[nodiscard]] const LpSolver& lp_solver() const { return *lp_solver_; }

  [[nodiscard]] LiteralSet enabled_literals() const final;

 protected:
  void CreateCheckpoint() override;

  /**
   * Update the @ref model_ with the bounds of the variables determined by the enabled literals.
   * @pre The solver must be consolidated.
   * @pre There are no rows in the lp problem, only bounds
   */
  void UpdateModelBounds();
  void UpdateModelSolution() override;
  /**
   * Notify the SAT solver that the current LP problem is infeasible by calling @p conflict_cb with the explanation.
   * @param conflict_cb conflict callback to be called with the explanation
   */
  void NotifyInfeasible(const ConflictCallback& conflict_cb) const;

  /** Set the bounds of the variables in the LP solver.  */
  virtual void EnableVarBound();

  /**
   * Disable all disabled spx rows from the LP solver.
   *
   * Whether a row is disabled or not is determined by the @ref theory_row_state_ field,
   * where a true value means the row is enabled and a false value means the row is disabled.
   */
  void DisableNotEnabledRows();

  std::vector<bool> rows_state_;             ///< Whether each LP row is enabled or not.
  std::vector<bool> rows_state_checkpoint_;  ///< Whether each LP row is enabled or not. Will be used to backtrack.

  std::unique_ptr<LpSolver> lp_solver_;  ///< Exact LP solver
};

}  // namespace dlinear
