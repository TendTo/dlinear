/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * SoplexTheorySolver class.
 */
#pragma once

#ifndef DLINEAR_ENABLED_SOPLEX
#error SoPlex is not enabled. Please enable it by adding "--//tools:enable_soplex" to the bazel command.
#endif

#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "dlinear/libs/libgmp.h"
#include "dlinear/libs/libsoplex.h"
#include "dlinear/solver/LpRowSense.h"
#include "dlinear/solver/TheorySolver.h"
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
class SoplexTheorySolver : public TheorySolver {
 public:
  explicit SoplexTheorySolver(PredicateAbstractor& predicate_abstractor,
                              const std::string& class_name = "SoplexTheorySolver");

  void AddVariable(const Variable& var) override;
  void AddLiterals() override;
  void Consolidate(const Box& box) override;
  void Reset() override;

 protected:
  static mpq_class infinity_;   ///< Positive infinity
  static mpq_class ninfinity_;  ///< Negative infinity

  void UpdateModelBounds() override;
  void UpdateModelSolution() override;
  void UpdateExplanation(LiteralSet& explanation) override;

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
  soplex::DSVectorRational ParseRowCoeff(const Formula& formula);
  /**
   * Set the coefficients to apply to @p var on a specific row.
   * @param coeffs vector of coefficients to apply to the decisional variables
   * @param var variable to set the coefficients for
   * @param value value to set the coefficients to
   */
  void SetSPXVarCoeff(soplex::DSVectorRational& coeffs, const Variable& var, const mpq_class& value) const;
  void CreateArtificials(int spx_row);

  /**
   * Get the infeasibility ray of the LP problem.
   *
   * This will return the Farkas ray, which can be used to find the infeasible core.
   * The infeasible constraints will have the same indexes as the non-zero elements in the Farkas ray.
   * @note The infeasible core is not guaranteed to be minimal
   * @pre The LP problem must be infeasible
   * @pre @code farkas_ray.size() == num_rows @endcode
   * @param[out] farkas_ray Farkas ray
   */
  void GetSpxInfeasibilityRay(soplex::VectorRational& farkas_ray);
  /**
   * Get the infeasibility rays of the LP problem.
   *
   * This will return the Farkas ray and use it to compute the bounds ray.
   * Combinind both it is possible to to find an even more precise infeasible core.
   * The infeasible constraints will have the same indexes as the non-zero elements in the Farkas ray.
   * Furthermore, given the Farkas ray @f$y@f$, we get an infeasible linear inequality @f$y^T A x \le y^T b@f$.
   * Therefore, even setting @f$x_i@f$ to the bound that minimises @f$y^T A x@f$, that minimum is still @f$> y^T b@f$,
   * but tells which bound to include in the explanation.
   * @note The infeasible core is not guaranteed to be minimal
   * @pre The LP problem must be infeasible
   * @pre @code farkas_ray.size() == num_rows @endcode
   * @pre @code bounds_ray.size() == num_cols - 1 @endcode
   * @pre All the element in @p bounds_ray must be @ref BoundViolationType::NO_BOUND_VIOLATION
   * @param[out] farkas_ray Farkas ray
   * @param[out] bounds_ray information about the bounds that are violated
   */
  void GetSpxInfeasibilityRay(soplex::VectorRational& farkas_ray, std::vector<BoundViolationType>& bounds_ray);

  /**
   * Get all active rows in the current solution.
   *
   * An active row is a row where the sum of the coefficients times the current solution is equal to either the
   * lower or upper bound of the row.
   * @note The problem must be feasible and a solution must have been found before calling this function.
   * @return vector of active rows with their value
   */
  std::vector<std::pair<int, soplex::Rational>> GetActiveRows();
  /**
   * Get active rows in the current solution among the rows in @p spx_rows.
   *
   * An active row is a row where the sum of the coefficients times the current solution is equal to either the
   * lower or upper bound of the row.
   * @note The problem must be feasible and a solution must have been found before calling this function.
   * @param spx_rows rows to check
   * @return vector of active rows among @p spx_rows with their value
   */
  std::vector<std::pair<int, soplex::Rational>> GetActiveRows(const std::vector<int>& spx_rows);
  /**
   * Check if the @p spx_row is active.
   *
   * An active row is a row where the sum of the coefficients times the current solution is equal to either the
   * lower or upper bound of the row.
   * @note The problem must be feasible and a solution must have been found before calling this function.
   * @param spx_row row to check
   * @return the value of the row if it is active
   * @return std::nullopt if the row is not active
   */
  std::optional<soplex::Rational> IsRowActive(int spx_row);
  /**
   * Check if the @p spx_row is active with value @p value.
   *
   * An active row is a row where the sum of the coefficients times the current solution is equal to either the
   * lower or upper bound of the row.
   * The value must be equal to @p value for the row to be considered active in this case.
   * @note The problem must be feasible and a solution must have been found before calling this function.
   * @param spx_row row to check
   * @param value value the row must be equal to in order to be considered active
   * @return true if the row is active with value @p value
   * @return false if the row is not active or if the value is not equal to @p value
   */
  bool IsRowActive(int spx_row, const soplex::Rational& value);

  soplex::SoPlex spx_;  ///< SoPlex exact LP solver

  soplex::LPColSetRational spx_cols_;  ///< Columns of the LP problem
  soplex::LPRowSetRational spx_rows_;  ///< Rows of the LP problem

  std::vector<mpq_class> spx_rhs_;     ///< Right-hand side of the rows
  std::vector<LpRowSense> spx_sense_;  ///< Sense of the rows
};

}  // namespace dlinear
