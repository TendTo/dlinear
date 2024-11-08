/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "LpSolver.h"

#include <ostream>

#include "dlinear/solver/theory_solver/qf_lra/SoplexLpSolver.h"
#include "dlinear/util/error.h"

namespace dlinear {

LpSolver::LpSolver(const Config& config, const std::string& class_name)
    : config_{config},
      stats_{config.with_timings(), class_name, "Total time spent in Optimise", "Total # of Optimise"} {}

std::unique_ptr<LpSolver> LpSolver::GetInstance(const Config& config) {
  switch (config.lp_solver()) {
    case Config::LPSolver::SOPLEX:
      return std::make_unique<SoplexLpSolver>(config);
    default:
      DLINEAR_UNREACHABLE();
  }
}
void LpSolver::Backtrack() {
  DLINEAR_DEBUG("LpSolver::Backtrack()");
  solution_.reset();
  objective_value_.reset();
  infeasible_rows_.reset();
  infeasible_bounds_.reset();
}
void LpSolver::UpdateModelWithSolution(Box& model) {
  DLINEAR_DEBUG("LpSolver::UpdateModelWithSolution()");
  DLINEAR_ASSERT(solution().has_value(), "LpSolver::UpdateModelWithSolution() called without a solution.");
  for (int i = 0; i < static_cast<int>(solution().value().size()); ++i) {
    model[lp_col_to_var().at(i)] = solution().value().at(i);
  }
}
void LpSolver::AddColumn(const Variable& var) {
  if (var_to_lp_col_.contains(var)) return;  // The variable is already accounted  in a column

  // Create a mapping between the variable and the lp column index
  var_to_lp_col_.emplace(var, var_to_lp_col_.size());
  lp_col_to_var_.emplace_back(var);

  // Add the column to the LP solver
  AddColumn();
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
      os << solver.lp_col_to_var().at(i) << " = " << solver.solution().value().at(i) << ", ";
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
      os << solver.lp_col_to_var().at(std::abs(s)) << (s < 0 ? " LB " : " UB ") << ", ";
    }
  }
  os << "}";
  return os;
}

}  // namespace dlinear
