/**
 * @file SoplexTheorySolver.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Theory solver using SoPlex.
 *
 * SoPlex is an exact LP solver written in C++.
 * It uses a mixture of techniques, from iterative refinement to precision boosting, in order to efficiently solve LPs
 * exactly.
 */
#pragma once

#ifndef DLINEAR_ENABLED_SOPLEX
#error SoPlex is not enabled. Please enable it by adding "--//tools:enable_soplex" to the bazel command.
#endif

#include <optional>
#include <vector>

#include "dlinear/libs/soplex.h"
#include "dlinear/solver/LpRowSense.h"
#include "dlinear/solver/TheorySolver.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"

namespace dlinear {

class SoplexTheorySolver : public TheorySolver {
 public:
  explicit SoplexTheorySolver(PredicateAbstractor& predicate_abstractor, const Config& config = Config{});

  void AddVariable(const Variable& var) override;

  void Reset(const Box& box) override;

 protected:
  static mpq_class infinity_;   ///< Positive infinity
  static mpq_class ninfinity_;  ///< Negative infinity

  void UpdateModelBounds() override;
  void UpdateExplanation(LiteralSet& explanation) override;

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

  /** Set the bounds of the variables in the LP solver.  */
  virtual void EnableSPXVarBound();

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
   *
   * The free variables are collected from the state of the solver.
   * @pre The row's coefficients must have been set correctly before calling this function
   * @pre The row's truth value must have been updated correctly
   * @param spx_row index of the row to enable
   * @param truth truth value of the row
   */
  void EnableSpxRow(int spx_row, bool truth);
  /**
   * Enable the @p spx_row row for the LP solver.
   * @pre The row's coefficients must have been set correctly before calling this function
   * @param spx_row index of the row to enable
   * @param free_vars free variables appearing in the row
   */
  void EnableSpxRow(int spx_row, const Variables& free_vars);
  /**
   * Enable the @p spx_row row for the LP solver.
   * @pre The row's coefficients must have been set correctly before calling this function
   * @param spx_row index of the row to enable
   * @param truth truth value of the row
   * @param free_vars free variables appearing in the row
   */
  virtual void EnableSpxRow(int spx_row, bool truth, const Variables& free_vars) = 0;

  /**
   * Parse a row and return the vector of coefficients to apply to the decisional variables.
   *
   * Parse an formula representing a row in order to produce store the rhs term in @ref spx_rhs_ and create a
   * vector of coefficients for the row to pass to the LP solver
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

  soplex::SoPlex spx_;  ///< SoPlex exact LP solver

  std::vector<mpq_class> spx_rhs_;     ///< Right-hand side of the rows
  std::vector<LpRowSense> spx_sense_;  ///< Sense of the rows
};

}  // namespace dlinear
