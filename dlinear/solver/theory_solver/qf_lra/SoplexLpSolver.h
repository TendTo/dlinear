/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * SoplexLpSolver class.
 */
#pragma once

#ifndef DLINEAR_ENABLED_SOPLEX
#error SoPlex is not enabled. Please enable it by adding "--//tools:enable_soplex" to the bazel command.
#endif

#include "dlinear/libs/libsoplex.h"
#include "dlinear/solver/theory_solver/qf_lra/LpSolver.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

/**
 * Linear programming solver using [SoPlex](https://soplex.zib.de/).
 */
class SoplexLpSolver : public LpSolver {
 public:
  explicit SoplexLpSolver(const Config& config, const std::string& class_name = "SoplexLpSolver");

  [[nodiscard]] int num_columns() const final;
  [[nodiscard]] int num_rows() const final;

  void ReserveColumns(int num_columns) final;
  void ReserveRows(int num_rows) final;
  void AddColumn() final;
  void AddRow(const Formula& formula, LpRowSense sense) final;
  void SetObjective(int column, const mpq_class& value) final;

  void EnableRow(int row, LpRowSense sense, const mpq_class& rhs) final;
  void DisableRow(int row) final;

  void EnableBound(int column, LpColBound bound, const mpq_class& value) final;
  void EnableBound(int column, const mpq_class& lb, const mpq_class& ub) final;
  void DisableBound(int column) final;

  void Consolidate() final;
  void Backtrack() final;

#ifndef NDEBUG
  void Dump() final;
#endif

 private:
  LpResult OptimiseCore(mpq_class& precision) final;
  /**
   * Parse a @p formula and return the vector of coefficients to apply to the decisional variables.
   *
   * It will store the rhs term in @ref rhs_ and create a vector of coefficients for the row.
   * @param formula symbolic formula representing the row
   * @return vector of coefficients to apply to the decisional variables in the row
   */
  soplex::DSVectorRational ParseRowCoeff(const Formula& formula);
  /**
   * Set the coefficients to apply to @p var on a specific row.
   *
   * The coefficient is set in @p coeff.
   * @param coeffs[out] vector of coefficients to apply to the decisional variables
   * @param var variable to set the coefficients for
   * @param value value to set the coefficients to
   */
  void SetVarCoeff(soplex::DSVectorRational& coeffs, const Variable& var, const mpq_class& value) const;

  /**
   * Use the result from the lp solver to update the solution vector and objective value.
   *
   * The lp solver was able to find a feasible solution to the problem.
   * The useful information will be stored in @ref objective_value_ and @ref solution_.
   * On the other hand, both @ref infeasible_rows_ and @ref infeasible_bounds_ will be cleared.
   */
  void UpdateFeasible();
  /**
   * Use the result from the lp solver to update the infeasible ray with the conflict that has been detected.
   *
   * This will allow the SAT solver to find a new assignment without the conflict.
   * The useful information will be stored in @ref infeasible_rows_ and @ref infeasible_bounds_.
   * On the other hand, both @ref objective_value_ and @ref solution_ will be cleared.
   *
   * More formally, we can use the infeasible ray @f$ y @f$ to create the linear inequality @f$ (y^T A) x \le y^T b @f$,
   * which is infeasible over the local bounds.
   * In other words, even setting each element of @f$ x @f$ to the bound that minimise @f$ (y^A) x @f$,
   * its value is still greater than @f$ y^T b @f$.
   */
  void UpdateInfeasible();

  soplex::SoPlex spx_;  ///< SoPlex LP solver

  soplex::LPColSetRational spx_cols_;  ///< Columns of the LP problem
  soplex::LPRowSetRational spx_rows_;  ///< Rows of the LP problem

  soplex::Rational rninfinity_;  ///< Rational negative infinity
  soplex::Rational rinfinity_;   ///< Rational positive infinity
};

}  // namespace dlinear
