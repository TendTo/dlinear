/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * SoplexTheorySolver class.
 */
#pragma once

#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/theory_solver/TheorySolver.h"
#include "dlinear/solver/theory_solver/qf_lra/LpRowSense.h"
#include "dlinear/solver/theory_solver/qf_lra/LpSolver.h"
#include "dlinear/solver/theory_solver/qf_lra/QfLraTheorySolver.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"

namespace dlinear {

/**
 * SoPlex is an exact LP solver written in C++.
 * It uses a mixture of techniques, from iterative refinement to precision boosting, in order to efficiently solve LPs
 * exactly.
 */
class LpTheorySolver : public QfLraTheorySolver {
 public:
  explicit LpTheorySolver(PredicateAbstractor& predicate_abstractor, const std::string& class_name = "LpTheorySolver");

  void AddVariable(const Variable& var) override;
  void AddLiterals() override;
  void Consolidate(const Box& box) override;
  void Backtrack() override;

 protected:
  void UpdateModelBounds();
  void UpdateModelSolution() override;
  void UpdateExplanation(LiteralSet& explanation);

  /** Set the bounds of the variables in the LP solver.  */
  virtual void EnableSpxVarBound();

  /**
   * Enable the @p spx_row row for the LP solver.
   *
   * The truth value and the free variables are collected from the state of the solver.
   * @pre The row's coefficients must have been set correctly before calling this function
   * @pre The row's truth value must have been updated correctly
   * @pre The row's free variables must have been updated correctly
   * @param spx_row index of the row to enable
   */
  void EnableSpxRow(int spx_row);
  /**
   * Enable the @p spx_row row for the LP solver.
   * @pre The row's coefficients must have been set correctly before calling this function
   * @param spx_row index of the row to enable
   * @param truth truth value of the row
   */
  virtual void EnableSpxRow(int spx_row, bool truth) = 0;

  /**
   * Disable all disabled spx rows from the LP solver.
   *
   * Whether a row is disabled or not is determined by the @ref theory_row_state_ field,
   * where a true value means the row is enabled and a false value means the row is disabled.
   */
  void DisableSpxRows();

  /**
   * Parse a @p formula and return the vector of coefficients to apply to the decisional variables.
   *
   * It will store the rhs term in @ref spx_rhs_ and create a vector of coefficients for the row.
   * @param formula symbolic formula representing the row
   * @return vector of coefficients to apply to the decisional variables in the row
   */
  std::unordered_map<int, mpq_class> ParseRowCoeff(const Formula& formula);
  /**
   * Set the coefficients to apply to @p var on a specific row.
   * @param coeffs vector of coefficients to apply to the decisional variables
   * @param var variable to set the coefficients for
   * @param value value to set the coefficients to
   */
  void SetSPXVarCoeff(std::unordered_map<int, mpq_class>& coeffs, const Variable& var, const mpq_class& value) const;

  std::unordered_map<Variable, int> var_to_lp_col_;  ///< Variable ⇔ lp column.
                                                     ///< The Variable is the one created by the PredicateAbstractor
                                                     ///< The column is the one used by the lp solver.
  std::vector<Variable> lp_col_to_var_;              ///< Theory column ⇔ Variable.
                                                     ///< The column is the one used by the lp solver.
                                                     ///< The Variable is the one created by the PredicateAbstractor
  std::unordered_map<Variable, int> lit_to_lp_row_;  ///< Literal ⇔ lp row.
                                                     ///< The literal is the one created by the PredicateAbstractor
                                                     ///< The row is the constraint used by the lp solver.
  std::vector<Literal> lp_row_to_lit_;               ///< Theory row ⇔ Literal
                                                     ///< The row is the constraint used by the lp solver.
                                                     ///< The literal is the one created by the PredicateAbstractor.
                                                     ///< It may not contain simple bounds
  std::vector<bool> lp_rows_state_;                  ///< Whether each lp row is enabled or not.

  std::unique_ptr<LpSolver> lp_solver_;  ///< Exact LP solver
};

}  // namespace dlinear
