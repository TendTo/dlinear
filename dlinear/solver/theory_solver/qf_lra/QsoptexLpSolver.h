/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * QsoptexLpSolver class.
 */
#pragma once

#ifndef DLINEAR_ENABLED_QSOPTEX
#error QSopt_ex is not enabled. Please enable it by adding "--//tools:enable_qsoptex" to the bazel command.
#endif

#include "dlinear/libs/libqsopt_ex.h"
#include "dlinear/solver/theory_solver/qf_lra/LpSolver.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

/**
 * Linear programming solver using [QSopt_ex](https://www.math.uwaterloo.ca/~bico/qsopt/ex/).
 */
class QsoptexLpSolver : public LpSolver {
 public:
  explicit QsoptexLpSolver(const Config& config, const std::string& class_name = "QsoptexLpSolver");
  ~QsoptexLpSolver() override;

  [[nodiscard]] int num_columns() const override;
  [[nodiscard]] int num_rows() const override;

  void AddColumn() final;
  void AddRow(const Formula& formula, LpRowSense sense) final;
  void SetObjective(int column, const mpq_class& value) final;

  void EnableRow(int row, LpRowSense sense, const mpq_class& rhs) final;
  void DisableRow(int row) final;

  void EnableBound(int column, LpColBound bound, const mpq_class& value) final;
  void EnableBound(int column, const mpq_class& lb, const mpq_class& ub) final;
  void DisableBound(int column) final;

#ifndef NDEBUG
  void Dump() final;
#endif

 private:
  LpResult OptimiseCore(mpq_class& precision) final;

  /**
   * Parse a @p formula and set the coefficient for each decisional variable appearing in it,
   * while also storing the rhs term in @ref rhs_.
   * @param row row to set the coefficients for
   * @param formula symbolic formula representing the row
   */
  void SetRowCoeff(int row, const Formula& formula);
  /**
   * Set the coefficients to apply to @p var on a specific @p row.
   * @param row row to set the coefficients for
   * @param var variable to set the coefficients for
   * @param value value to set the coefficients to
   */
  void SetVarCoeff(int row, const Variable& var, const mpq_class& value) const;

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

  mpq_QSprob qsx_;  ///< QSopt_ex LP solver

  qsopt_ex::MpqArray ray_;  ///< Ray of the last infeasible solution
  qsopt_ex::MpqArray x_;    ///< Solution vector
};

}  // namespace dlinear
