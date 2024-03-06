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
  static mpq_class infinity_;
  static mpq_class ninfinity_;

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

  void SetSPXVarBound();
  /**
   * Parse a row and return the vector of coefficients to apply to the decisional variables.
   *
   * Parse an formula representing a row in order to produce store the rhs term in @link spx_rhs_ @endlink and create a
   * vector of coefficients for the row to pass to the LP solver
   * @param formula symbolic formula representing the row
   * @return vector of coefficients to apply to the decisional variables in the row
   */
  soplex::DSVectorRational ParseRowCoeff(const Formula& formula);
  void SetSPXVarCoeff(soplex::DSVectorRational& coeffs, const Variable& var, const mpq_class& value) const;
  void CreateArtificials(int spx_row);

  // Exact LP solver (SoPlex)
  soplex::SoPlex spx_;
  soplex::VectorRational spx_lower_;
  soplex::VectorRational spx_upper_;

  std::vector<mpq_class> spx_rhs_;
  std::vector<LpRowSense> spx_sense_;
};

}  // namespace dlinear
