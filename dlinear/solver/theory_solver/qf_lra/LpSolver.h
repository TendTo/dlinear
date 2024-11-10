/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * LpSolver class.
 */
#pragma once

#include <iosfwd>
#include <unordered_map>

#include "dlinear/libs/libgmp.h"
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
 */
class LpSolver {
 public:
  static std::unique_ptr<LpSolver> GetInstance(const Config& config);

  /**
   * Construct a new LpSolver object with the given @p config .
   * @param config configuration to use
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
  /** @getter{objective value\, if the lp is feasible\,, lp solver} */
  [[nodiscard]] const std::optional<mpq_class>& objective_value() const { return objective_value_; }
  /** @getter{solution\, if the lp is feasible\,, lp solver} */
  [[nodiscard]] const std::optional<std::vector<mpq_class>>& solution() const { return solution_; }
  /** @getter{infeasible\, if the lp is infeasible\,, lp solver} */
  [[nodiscard]] const std::optional<std::vector<int>>& infeasible_rows() const { return infeasible_rows_; }
  /** @getter{solution\, if the lp is infeasible\,, lp solver} */
  [[nodiscard]] const std::optional<std::vector<int>>& infeasible_bounds() const { return infeasible_bounds_; }
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

  virtual void ReserveColumns(int size);
  virtual void ReserveRows(int size);

  virtual void AddColumn() = 0;
  void AddColumn(const Variable& var);

  void AddRow(const Variable& formula_var, const Formula& formula);
  void AddRow(const Variable& formula_var, const Formula& formula, LpRowSense sense);
  void AddRow(const Formula& formula);
  virtual void AddRow(const Formula& formula, LpRowSense sense) = 0;

  virtual void SetObjective(int column, const mpq_class& value) = 0;

  void UpdateLiteralAssignment(const Variable& var, bool truth);
  void UpdateLiteralAssignment(int row, bool truth);

  void EnableRows();
  void EnableRow(int row);
  void EnableRow(int row, LpRowSense sense);
  virtual void EnableRow(int row, LpRowSense sense, const mpq_class& rhs) = 0;
  virtual void DisableRow(int row) = 0;

  virtual void EnableBound(int column, LpColBound bound, const mpq_class& value) = 0;
  virtual void EnableBound(int column, const mpq_class& lb, const mpq_class& ub) = 0;
  virtual void DisableBound(int column) = 0;

  void EnableBound(const Variable& var, LpColBound bound, const mpq_class& value);
  void EnableBound(const Variable& var, const mpq_class& lb, const mpq_class& ub);
  void DisableBound(const Variable& var);

  void DisableAll();

  void SetObjective(const std::unordered_map<int, mpq_class>& objective);
  void SetObjective(const std::vector<mpq_class>& objective);

  virtual void Consolidate();
  virtual void Backtrack();

  /**
   * Optimise the LP problem with the given @p precision .
   *
   * The actual precision will be returned in the @p precision parameter.
   * @param precision[in, out] desired precision for the optimisation that becomes the actual precision achieved
   */
  LpResult Optimise(mpq_class& precision);

  void UpdateModelWithSolution(Box& model);

#ifndef NDEBUG
  virtual void Dump() = 0;
#endif

 protected:
  virtual LpResult OptimiseCore(mpq_class& precision) = 0;

  const Config& config_;  ///< Configuration to use
  IterationStats stats_;  ///< Statistics of the solver

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

  std::optional<mpq_class> objective_value_;           ///< Objective value
  std::optional<std::vector<mpq_class>> solution_;     ///< Solution vector
  std::optional<std::vector<int>> infeasible_rows_;    ///< Set of infeasible rows detected by the Farkas ray
  std::optional<std::vector<int>> infeasible_bounds_;  ///< Set of infeasible bounds detected by the Farkas ray.
  ///< If the row index is negative, the lower bound is to blame, else the infeasibility arises from the upper bound

  mpq_class ninfinity_;  ///< Negative infinity threshold value
  mpq_class infinity_;   ///< Infinity threshold value
};

std::ostream& operator<<(std::ostream& os, const LpSolver& solver);

}  // namespace dlinear
