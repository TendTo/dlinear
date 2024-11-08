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
  explicit LpSolver(const Config& config, const std::string& class_name = "LpSolver");
  virtual ~LpSolver() = default;

  /** @getter{number of columns, lp solver} */
  [[nodiscard]] virtual int num_columns() const = 0;
  /** @getter{number of rows, lp solver} */
  [[nodiscard]] virtual int num_rows() const = 0;
  /** @getter{negative infinity threshold value, lp solver} */
  [[nodiscard]] virtual const mpq_class& ninfinity() const = 0;
  /** @getter{infinity threshold value, lp solver} */
  [[nodiscard]] virtual const mpq_class& infinity() const = 0;
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
  /** @getter{senses of the constraints, lp solver} */
  [[nodiscard]] const std::vector<LpRowSense>& senses() const { return senses_; }
  /** @getter{map from real variables to columns, lp solver} */
  [[nodiscard]] const std::unordered_map<Variable, int>& var_to_lp_col() const { return var_to_lp_col_; }
  /** @getter{map from columns to real variables, lp solver} */
  [[nodiscard]] const std::vector<Variable>& lp_col_to_var() const { return lp_col_to_var_; }

  virtual void ReserveColumns(int size) = 0;
  virtual void ReserveRows(int size) = 0;

  virtual void AddColumn() = 0;
  void AddColumn(const Variable& var);
  virtual void AddRow(const Formula& formula) = 0;
  virtual void SetObjective(int column, const mpq_class& value) = 0;

  virtual void EnableRow(int row, LpRowSense sense) = 0;
  virtual void EnableRow(int row, LpRowSense sense, const mpq_class& rhs) = 0;
  virtual void DisableRow(int row) = 0;

  virtual void EnableBound(int column, LpColBound bound, const mpq_class& value) = 0;
  virtual void EnableBound(int column, const mpq_class& lb, const mpq_class& ub) = 0;
  virtual void DisableBound(int column) = 0;

  virtual void DisableAll() = 0;

  virtual void SetObjective(const std::unordered_map<int, mpq_class>& objective) = 0;

  virtual void Consolidate() = 0;
  virtual void Backtrack();
  /**
   * Optimise the LP problem with the given @p precision .
   *
   * The actual precision will be returned in the @p precision parameter.
   * @param precision[in, out] desired precision for the optimisation that becomes the actual precision achieved
   */
  virtual LpResult Optimise(mpq_class& precision) = 0;

  void UpdateModelWithSolution(Box& model);

#ifndef NDEBUG
  virtual void Dump() = 0;
#endif

 protected:
  const Config& config_;  ///< Configuration to use
  IterationStats stats_;  ///< Statistics of the solver

  std::vector<mpq_class> rhs_;
  std::vector<LpRowSense> senses_;

  std::unordered_map<Variable, int> var_to_lp_col_;  ///< Mapping from real variables to columns
  std::vector<Variable> lp_col_to_var_;              ///< Mapping from columns to real variables

  std::optional<mpq_class> objective_value_;           ///< Objective value
  std::optional<std::vector<mpq_class>> solution_;     ///< Solution vector
  std::optional<std::vector<int>> infeasible_rows_;    ///< Set of infeasible rows detected by the Farkas ray
  std::optional<std::vector<int>> infeasible_bounds_;  ///< Set of infeasible bounds detected by the Farkas ray.
  ///< If the row index is negative, the lower bound is to blame, else the infeasibility arises from the upper bound
};

std::ostream& operator<<(std::ostream& os, const LpSolver& solver);

}  // namespace dlinear
