/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "LpSolver.h"

#include <ostream>
#include <utility>

#include "dlinear/solver/theory_solver/qf_lra/QsoptexLpSolver.h"
#include "dlinear/solver/theory_solver/qf_lra/SoplexLpSolver.h"
#include "dlinear/util/error.h"

namespace dlinear {

LpSolver::LpSolver(const Config& config, mpq_class ninfinity, mpq_class infinity, const std::string& class_name)
    : config_{config},
      stats_{config.with_timings(), class_name, "Total time spent in Optimise", "Total # of Optimise"},
      rhs_{},
      senses_{},
      var_to_col_{},
      col_to_var_{},
      lit_to_row_{},
      row_to_lit_{},
      objective_value_{},
      solution_{},
      infeasible_rows_{},
      infeasible_bounds_{},
      ninfinity_{std::move(ninfinity)},
      infinity_{std::move(infinity)} {}

std::unique_ptr<LpSolver> LpSolver::GetInstance(const Config& config) {
  switch (config.lp_solver()) {
    case Config::LPSolver::SOPLEX:
      return std::make_unique<SoplexLpSolver>(config);
    case Config::LPSolver::QSOPTEX:
      return std::make_unique<QsoptexLpSolver>(config);
    default:
      DLINEAR_UNREACHABLE();
  }
}

void LpSolver::AddColumn(const Variable& var) {
  DLINEAR_ASSERT(!var_to_col_.contains(var), "Variable already exists in the LP.");
  // Update indexes
  var_to_col_.emplace(var, var_to_col_.size());
  col_to_var_.emplace_back(var);
  // Add a column representing this variable to the lp solver
  AddColumn();

  DLINEAR_ASSERT(static_cast<std::size_t>(num_columns()) == col_to_var_.size(), "incorrect theory_col_to_var_.size()");
  DLINEAR_ASSERT(static_cast<std::size_t>(num_columns()) == var_to_col_.size(), "incorrect theory_var_to_col_.size()");
}

void LpSolver::Backtrack() {
  DLINEAR_DEBUG("LpSolver::Backtrack()");
  solution_.reset();
  objective_value_.reset();
  infeasible_rows_.reset();
  infeasible_bounds_.reset();
}
void LpSolver::Consolidate() {}

void LpSolver::UpdateModelWithSolution(Box& model) {
  DLINEAR_DEBUG("LpSolver::UpdateModelWithSolution()");
  DLINEAR_ASSERT(solution().has_value(), "LpSolver::UpdateModelWithSolution() called without a solution.");
  for (int i = 0; i < static_cast<int>(solution().value().size()); ++i) {
    model[col_to_var_.at(i)] = solution().value().at(i);
  }
}
void LpSolver::AddRow(const Variable& formula_var, const Formula& formula) {
  AddRow(formula_var, formula, parseLpSense(formula));
}
void LpSolver::AddRow(const Formula& formula) { AddRow(formula, parseLpSense(formula)); }
void LpSolver::AddRow(const Variable& formula_var, const Formula& formula, LpRowSense sense) {
  DLINEAR_ASSERT(!lit_to_row_.contains(formula_var), "Literal already exists in the LP.");
  // Update indexes
  lit_to_row_.emplace(formula_var, lit_to_row_.size());
  row_to_lit_.emplace_back(formula_var, true);
  // Add a row representing this formula to the lp solver
  AddRow(formula, sense);

  DLINEAR_ASSERT(static_cast<std::size_t>(num_rows()) == row_to_lit_.size(), "incorrect theory_row_to_lit_.size()");
  DLINEAR_ASSERT(static_cast<std::size_t>(num_rows()) == lit_to_row_.size(), "incorrect theory_row_to_lit_.size()");
  DLINEAR_ASSERT(static_cast<std::size_t>(num_rows()) == senses_.size(), "incorrect spx_sense_.size()");
  DLINEAR_ASSERT(static_cast<std::size_t>(num_rows()) == rhs_.size(), "incorrect spx_rhs_.size()");
}

void LpSolver::UpdateLiteralAssignment(const Variable& var, bool truth) {
  DLINEAR_ASSERT(lit_to_row_.contains(var), "Literal not found in the LP.");
  UpdateLiteralAssignment(lit_to_row_.at(var), truth);
}
void LpSolver::UpdateLiteralAssignment(int row, bool truth) {
  DLINEAR_ASSERT(0 <= row && row < num_rows(), "Row index out of bounds.");
  row_to_lit_.at(row).truth = truth;
}

void LpSolver::EnableBound(const Variable& var, LpColBound bound, const mpq_class& value) {
  EnableBound(var_to_col_.at(var), bound, value);
}
void LpSolver::EnableBound(const Variable& var, const mpq_class& lb, const mpq_class& ub) {
  EnableBound(var_to_col_.at(var), lb, ub);
}
void LpSolver::DisableBound(const Variable& var) { DisableBound(var_to_col_.at(var)); }
void LpSolver::EnableRows() {
  for (int i = 0; i < num_rows(); ++i) EnableRow(i);
}
void LpSolver::ReserveRows(int size) {
  DLINEAR_ASSERT(size >= 0, "Invalid number of rows.");
  rhs_.reserve(size);
  senses_.reserve(size);
  lit_to_row_.reserve(size);
  row_to_lit_.reserve(size);
}
void LpSolver::ReserveColumns(int size) {
  DLINEAR_ASSERT(size >= 0, "Invalid number of columns.");
  var_to_col_.reserve(size);
  col_to_var_.reserve(size);
}

void LpSolver::EnableRow(int row) { EnableRow(row, senses_.at(row), rhs_.at(row)); }
void LpSolver::EnableRow(int row, LpRowSense sense) { EnableRow(row, sense, rhs_.at(row)); }

void LpSolver::DisableAll() {
  for (int i = 0; i < num_columns(); i++) DisableBound(i);
  for (int i = 0; i < num_rows(); i++) DisableRow(i);
}

void LpSolver::SetObjective(const std::unordered_map<int, mpq_class>& objective) {
  for (const auto& [column, value] : objective) SetObjective(column, value);
}
void LpSolver::SetObjective(const std::vector<mpq_class>& objective) {
  for (int i = 0; i < static_cast<int>(objective.size()); ++i) SetObjective(i, objective.at(i));
}
LpResult LpSolver::Optimise(mpq_class& precision) {
  const TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();
  return OptimiseCore(precision);
}

std::ostream& operator<<(std::ostream& os, const LpSolver& solver) {
  if (dynamic_cast<const SoplexLpSolver*>(&solver)) {
    os << "SoplexLpSolver";
  } else {
    DLINEAR_UNREACHABLE();
  }
  os << " {";
  os << "num_columns: " << solver.num_columns() << ", ";
  os << "num_rows: " << solver.num_rows() << ", ";
  os << "ninfinity: " << solver.ninfinity() << ", ";
  os << "infinity: " << solver.infinity() << ", ";
  os << "stats: " << solver.stats() << ", ";
  os << "config: " << solver.config() << ", ";
  os << "objective_value: " << solver.objective_value().value_or(mpq_class{0}) << ", ";
  if (solver.objective_value().has_value()) {
    os << "solution: ";
    for (int i = 0; i < static_cast<int>(solver.solution().value().size()); ++i) {
      os << solver.col_to_var().at(i) << " = " << solver.solution().value().at(i) << ", ";
    }
  }
  if (solver.infeasible_rows().has_value()) {
    os << "infeasible_rows: ";
    for (const int s : solver.infeasible_rows().value()) {
      os << s << ", ";
    }
  }
  if (solver.infeasible_bounds().has_value()) {
    os << "infeasible_bounds: ";
    for (const int s : solver.infeasible_bounds().value()) {
      os << solver.col_to_var().at(std::abs(s)) << (s < 0 ? " LB " : " UB ") << ", ";
    }
  }
  os << "}";
  return os;
}

}  // namespace dlinear
