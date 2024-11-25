/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * LpSolver class.
 */
#pragma once

#include <iosfwd>
#include <optional>
#include <unordered_map>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/theory_solver/qf_lra/LpBoundViolation.h"
#include "dlinear/solver/theory_solver/qf_lra/LpColBound.h"
#include "dlinear/solver/theory_solver/qf_lra/LpResult.h"
#include "dlinear/solver/theory_solver/qf_lra/LpRowSense.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Stats.h"

namespace dlinear {

/**
 * Facade class that hides the underlying LP solver used by dlinear.
 *
 * It provides a common interface to interact with any number of LP solvers, implemented as subclasses.
 * An LP problem is defined as
 * @f[
 * \begin{array}{}
 *      & \max              & c^T x     \newline
 *      & \text{subject to} & A x \le b \newline
 *      &                   & l \le x \le u
 * \end{array}
 * @f]
 * where @f$ x @f$ is the vector of real variables, @f$ c @f$ is the vector of objective coefficients,
 * @f$ A @f$ is the matrix of coefficients of the constraints, @f$ b @f$ is the right-hand side of the constraints,
 * @f$ l @f$ is the vector of lower bounds, and @f$ u @f$ is the vector of upper bounds.
 *
 * If the problem is feasible, the solution vector @f$ x @f$ and the objective value are made available.
 * Otherwise, the Farekas ray  @f$ y @f$ is used to create the linear inequality @f$ (y^T A) x \le y^T b @f$,
 * which is infeasible over the local bounds.
 * In other words, even setting each element of @f$ x @f$ to the bound that minimise @f$ (y^A) x @f$,
 * its value is still greater than @f$ y^T b @f$.
 *
 * The usual workflow is as follows:
 * - For each real variable in the SMT problem, add a linked column with @ref AddColumn(const Variable&).
 * - For each symbolic formula in the SMT problem, add a linked row with @ref AddRow(const Variable&, const Formula&).
 * - Consolidate the LP problem with @ref Consolidate.
 * - Enable the active rows and bounds with @ref EnableRow and @ref EnableBound.
 * - Optimise the LP problem with @ref Optimise.
 *   - If the problem is feasible, update the model with @ref UpdateModelWithSolution.
 *   - If the problem is infeasible, generate an explanation using the infeasible rows and bounds.
 */
class LpSolver {
 public:
  static std::unique_ptr<LpSolver> GetInstance(const Config& config);

  /**
   * Construct a new LpSolver object with the given @p config .
   * @param config configuration to use
   * @param ninfinity negative infinity threshold value
   * @param infinity infinity threshold value
   * @param class_name name of the class
   */
  LpSolver(const Config& config, mpq_class ninfinity, mpq_class infinity, const std::string& class_name = "LpSolver");
  virtual ~LpSolver() = default;

  /** @getter{number of columns, lp solver} */
  [[nodiscard]] virtual int num_columns() const = 0;
  /** @getter{number of rows, lp solver} */
  [[nodiscard]] virtual int num_rows() const = 0;
  /** @getter{negative infinity threshold value, lp solver} */
  [[nodiscard]] const mpq_class& ninfinity() const { return ninfinity_; }
  /** @getter{infinity threshold value, lp solver} */
  [[nodiscard]] const mpq_class& infinity() const { return infinity_; }
  /** @getter{statistics, lp solver} */
  [[nodiscard]] const IterationStats& stats() const { return stats_; }
  /** @getter{configuration, lp solver} */
  [[nodiscard]] const Config& config() const { return config_; }
  /** @getter{primal solution\, if the lp is feasible\,, lp solver} */
  [[nodiscard]] const std::vector<mpq_class>& solution() const { return solution_; }
  /** @getter{dual solution\, if the lp is feasible\,, lp solver */
  [[nodiscard]] const std::vector<mpq_class>& dual_solution() const { return dual_solution_; }
  /** @getter{vector of rows responsible for the infeasibility\, if the lp is infeasible\,, lp solver} */
  [[nodiscard]] const std::vector<int>& infeasible_rows() const { return infeasible_rows_; }
  /**
   * @getter{vector of column bounds responsible for the infeasibility\, if the lp is infeasible\,, lp solver,
   * False means the lower bound is to blame, else it upper bound is at fault.}
   */
  [[nodiscard]] const std::vector<LpBoundViolation>& infeasible_bounds() const { return infeasible_bounds_; }
  /** @getter{right-hand side of the constraints, lp solver} */
  [[nodiscard]] const std::vector<mpq_class>& rhs() const { return rhs_; }
  /** @getter{maps from and to SMT variables to LP columns/rows, lp solver} */
  [[nodiscard]] const std::unordered_map<Variable, int>& var_to_col() const { return var_to_col_; }
  /** @getter{maps from and to SMT variables to LP columns/rows, lp solver} */
  [[nodiscard]] const std::vector<Variable>& col_to_var() const { return col_to_var_; }
  /** @getter{maps from and to SMT variables to LP columns/rows, lp solver} */
  [[nodiscard]] const std::unordered_map<Variable, int>& lit_to_row() const { return lit_to_row_; }
  /** @getter{maps from and to SMT variables to LP columns/rows, lp solver} */
  [[nodiscard]] const std::vector<Literal>& row_to_lit() const { return row_to_lit_; }
  /** @getter{sense of the constraints, lp solver} */
  [[nodiscard]] const std::vector<LpRowSense>& senses() const { return senses_; }
  /**
   * Shorthand notation to get the literal linked with row @p row.
   * @param row index of the row the literal is linked to
   * @return corresponding literal
   */
  [[nodiscard]] const Literal& lit(int row) const { return row_to_lit_.at(row); }
  /**
   * Shorthand notation to get the real variable linked with column @p column.
   * @param column index of the column the real variable is linked to
   * @return corresponding real variable
   */
  [[nodiscard]] const Variable& var(int column) const { return col_to_var_.at(column); }
  /**
   * Shorthand notation to get the row linked with the literal @p lit.
   * @param lit theory literal the row is linked to
   * @return corresponding row in the LP
   */
  [[nodiscard]] int row(const Literal& lit) const { return lit_to_row_.at(lit.var); }
  /**
   * Shorthand notation to get the column linked with the real variable @p var.
   * @param var real variable the column is linked to
   * @return corresponding column in the LP
   */
  [[nodiscard]] int column(const Variable& var) const { return var_to_col_.at(var); }

  /**
   * Reserve space for the given number of columns and rows.
   *
   * Can speed up the addition of columns if the guess is close to the actual number.
   * @param size number of columns to reserve
   */
  virtual void ReserveColumns(int size);
  /**
   * Reserve space for the given number of rows.
   *
   * Can speed up the addition of rows if the guess is close to the actual number.
   * @param size number of rows to reserve
   */
  virtual void ReserveRows(int size);

  /**
   * Add a new unbounded column to the LP problem.
   * @pre The column must be added before the LP problem is consolidated.
   */
  virtual void AddColumn() = 0;
  /**
   * Add a new bounded column to the LP problem.
   * @pre The column must be added before the LP problem is consolidated.
   * @param lb lower bound of the column
   * @param ub upper bound of the column
   */
  virtual void AddColumn(const mpq_class& lb, const mpq_class& ub) = 0;
  /**
   * Add a new bounded column to the LP problem with a given @p obj coefficient.
   * @pre The column must be added before the LP problem is consolidated.
   * @param obj objective coefficient of the column
   * @param lb lower bound of the column
   * @param ub upper bound of the column
   */
  virtual void AddColumn(const mpq_class& obj, const mpq_class& lb, const mpq_class& ub) = 0;
  /**
   * Add a new unbounded column to the LP problem  @p var .
   *
   * It also links the new column to the given @p var .
   * @pre The column must be added before the LP problem is consolidated.
   * @pre All other columns already in the LP problem have been linked as well.
   * @param var real variable this column is linked to
   */
  void AddColumn(const Variable& var);

  /**
   * Add a new row to the LP problem with the given @p formula .
   *
   * It also links the new row to the given @p formula_var .
   * @pre The row must be added before the LP problem is consolidated.
   * @pre All other rows already in the LP problem have been linked as well.
   * @param formula_var variable representing a literal this row is linked to
   * @param formula symbolic formula representing the row
   */
  void AddRow(const Variable& formula_var, const Formula& formula);
  /**
   * Add a new row to the LP problem with the given @p formula and @p sense .
   *
   * It also links the new row to the given @p formula_var .
   * @pre The row must be added before the LP problem is consolidated.
   * @pre All other rows already in the LP problem have been linked as well.
   * @param formula_var variable representing a literal this row is linked to
   * @param formula symbolic formula representing the row
   * @param sense sense of the row (e.g. <=, =, >=)
   */
  void AddRow(const Variable& formula_var, const Formula& formula, LpRowSense sense);
  /**
   * Add a new row to the LP problem with the given @p formula .
   * @pre The row must be added before the LP problem is consolidated.
   * @param formula symbolic formula representing the row
   */
  void AddRow(const Formula& formula);
  /**
   * Add a new row to the LP problem with the given @p formula and @p sense .
   * @pre The row must be added before the LP problem is consolidated.
   * @param formula symbolic formula representing the row
   * @param sense sense of the row (i.e. <=, =, >=)
   */
  virtual void AddRow(const Formula& formula, LpRowSense sense) = 0;

  /**
   * Set the truth value of the literal identified by @p var in @ref row_to_lit_ to the given @p truth value.
   * @param var variable representing the literal to update
   * @param truth new truth value for the literal
   */
  void UpdateLiteralAssignment(const Variable& var, bool truth);
  /**
   * Set the truth value of the literal identified by @p row in @ref row_to_lit_ to the given @p truth value.
   * @param row row representing the literal to update
   * @param truth new truth value for the literal
   */
  void UpdateLiteralAssignment(int row, bool truth);

  /** Enable all rows previously added in the LP problem. */
  void EnableRows();
  /**
   * Enable the row with index @p row in the LP problem.
   * @param row index of the row to enable
   */
  void EnableRow(int row);
  /**
   * Enable the row with index @p row in the LP problem and assign it the given @p sense .
   * @param row index of the row to enable
   * @param sense sense to assign the row (i.e. <=, =, >=)
   */
  void EnableRow(int row, LpRowSense sense);
  /**
   * Enable the row with index @p row in the LP problem and assign it the given @p sense and @p rhs .
   * @param row index of the row to enable
   * @param sense sense to assign the row (i.e. <=, =, >=)
   * @param rhs right-hand side of the row
   */
  virtual void EnableRow(int row, LpRowSense sense, const mpq_class& rhs) = 0;
  /**
   * Disable the row with index @p row in the LP problem.
   * @param row index of the row to disable
   */
  virtual void DisableRow(int row) = 0;

  /**
   * Enable the bound of the column with index @p column in the LP problem
   * and assign it the given @p bound and @p value .
   * @param column index of the column to enable
   * @param bound bound to assign the column (i.e. lower, upper, bounded, free)
   * @param value value to assign the bound
   */
  virtual void EnableBound(int column, LpColBound bound, const mpq_class& value) = 0;
  /**
   * Enable the bound of the column with index @p column in the LP problem
   * and assign it the given @p lb and @p ub .
   * @param column index of the column to enable
   * @param lb lower bound to assign the column
   * @param ub upper bound to assign the column
   */
  virtual void EnableBound(int column, const mpq_class& lb, const mpq_class& ub) = 0;
  /**
   * Disable the bound of the column with index @p column in the LP problem.
   * @param column index of the column to disable
   */
  virtual void DisableBound(int column) = 0;

  /**
   * Enable the bound linked to @p var and assign it the given @p bound and @p value .
   * @param var real variable linked to the column
   * @param bound bound to assign the variable (i.e. lower, upper, bounded, free)
   * @param value value to assign the bound
   */
  void EnableBound(const Variable& var, LpColBound bound, const mpq_class& value);
  /**
   * Enable the bound linked to @p var and assign it the given @p lb and @p ub .
   * @param var real variable linked to the column
   * @param lb lower bound to assign the variable
   * @param ub upper bound to assign the variable
   */
  void EnableBound(const Variable& var, const mpq_class& lb, const mpq_class& ub);
  /**
   * Disable the bound linked to @p var .
   * @param var real variable linked to the column
   */
  void DisableBound(const Variable& var);

  /** Disable all rows and bounds */
  void DisableAll();

  /**
   * Set the coefficient of the @p row constraint to apply at the @p column decisional variable.
   * @param row row of the constraint
   * @param column column containing the decisional variable to set the coefficient for
   * @param value new value of the coefficient
   */
  virtual void SetCoefficient(int row, int column, const mpq_class& value) = 0;

  /**
   * Set the objective coefficients of the LP problem to the given @p objective .
   * @param objective map from column index to objective coefficient
   */
  void SetObjective(const std::unordered_map<int, mpq_class>& objective);
  /**
   * Set the objective coefficients of the LP problem to the given @p objective .
   * @param objective
   */
  void SetObjective(const std::vector<mpq_class>& objective);
  /**
   * The the objective coefficient of the column corresponding to the give @p var to the given @p value .
   * @param var variable to set the objective for
   * @param value new objective coefficient for the column
   */
  void SetObjective(const Variable& var, const mpq_class& value);
  /**
   * The the objective coefficient of the given @p column to the given @p value .
   * @param column column to set the objective for
   * @param value new objective coefficient for the column
   */
  virtual void SetObjective(int column, const mpq_class& value) = 0;

  /**
   * Consolidate the LP problem, making sure all added rows and columns are ready to be enabled.
   *
   * Must be called after adding all the desired rows and columns and before any attempt at enabling or disabling them
   * or calling the @ref Optimise method.
   */
  virtual void Consolidate();
  /**
   * Ensure the solver is in a state that enables the solution of another LP problem.
   *
   * It does not enable or disable any row.
   */
  virtual void Backtrack();

  /**
   * Optimise the LP problem with the given @p precision .
   *
   * The result of the computation will be stored in @ref solution_ and @ref dual_solution_ if the problem is feasible,
   * and in @ref infeasible_rows_ and @ref infeasible_bounds_ otherwise.
   * If @p store_solution is false, the solution will not be stored, but the LpResult will still be returned.
   * The actual precision will be returned in the @p precision parameter.
   * @param[in,out] precision desired precision for the optimisation that becomes the actual precision achieved
   * @param store_solution whether the solution and dual solution should be stored
   * @return OPTIMAL if an optimal solution has been found and the return value of @p precision is @f$ = 0 @f$
   * @return DELTA_OPTIMAL if an optimal solution has been found and the return value of @p precision @f$\ge 0 @f$
   * @return UNBOUNDED if the problem is unbounded
   * @return INFEASIBLE if the problem is infeasible
   * @return ERROR if an error occurred
   */
  LpResult Optimise(mpq_class& precision, bool store_solution = true);

  /**
   * Update the model with the solution found by the LP solver.
   * @pre The last call to @ref Optimise discovered a feasible solution.
   * @param model box to update with the solution
   */
  void UpdateModelWithSolution(Box& model) const;

#ifndef NDEBUG
  virtual void Dump() = 0;
#endif

 protected:
  /**
   * Internal method that optimises the LP problem with the given @p precision .
   * @param precision desired precision for the optimisation
   * @param store_solution whether the solution and dual solution should be stored
   * @return OPTIMAL if an optimal solution has been found and the return value of @p precision is @f$ = 0 @f$
   * @return DELTA_OPTIMAL if an optimal solution has been found and the return value of @p precision @f$\ge 0 @f$
   * @return UNBOUNDED if the problem is unbounded
   * @return INFEASIBLE if the problem is infeasible
   * @return ERROR if an error occurred
   */
  virtual LpResult OptimiseCore(mpq_class& precision, bool store_solution) = 0;

  const Config& config_;  ///< Configuration to use
  IterationStats stats_;  ///< Statistics of the solver
  bool consolidated_;     ///< Whether the LP problem has been consolidated

  std::vector<mpq_class> rhs_;      ///< Right-hand side of the constraints
  std::vector<LpRowSense> senses_;  ///< Sense of the constraints (e.g. <=, =, >=)

  std::unordered_map<Variable, int> var_to_col_;  ///< Theory column ⇔ Variable.
                                                  ///< The column is the one used by the lp solver.
                                                  ///< The Variable is the one created by the PredicateAbstractor
  std::vector<Variable> col_to_var_;              ///< Literal ⇔ lp row.
                                                  ///< The literal is the one created by the PredicateAbstractor
                                                  ///< The row is the constraint used by the lp solver.
  std::unordered_map<Variable, int> lit_to_row_;  ///< Theory row ⇔ Literal
                                                  ///< The row is the constraint used by the lp solver.
                                                  ///< The literal is the one created by the PredicateAbstractor.
                                                  ///< It may not contain simple bounds
  std::vector<Literal> row_to_lit_;               ///< Variable ⇔ lp column.
                                                  ///< The Variable is the one created by the PredicateAbstractor
                                                  ///< The column is the one used by the lp solver.

  std::vector<mpq_class> solution_;                  ///< Solution vector
  std::vector<mpq_class> dual_solution_;             ///< Dual solution vector
  std::vector<int> infeasible_rows_;                 ///< Set of infeasible rows
  std::vector<LpBoundViolation> infeasible_bounds_;  ///< Set of infeasible bounds.

  mpq_class ninfinity_;  ///< Negative infinity threshold value
  mpq_class infinity_;   ///< Infinity threshold value
};

std::ostream& operator<<(std::ostream& os, const LpSolver& solver);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::LpSolver);

#endif
