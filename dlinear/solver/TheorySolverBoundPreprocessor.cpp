/**
 * @file TheorySolverBoundPreprocessor.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "TheorySolverBoundPreprocessor.h"

#include <list>
#include <unordered_set>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/Context.h"
#include "dlinear/solver/TheorySolver.h"

namespace dlinear {

namespace {
// std::set<LiteralSet> cartesian_product(const std::set<LiteralSet>& a, const std::set<LiteralSet>& b,
//                                        const std::set<LiteralSet>& c) {
//   std::set<LiteralSet> result;
//   for (const auto& a_set : a) {
//     for (const auto& b_set : b) {
//       for (const auto& c_set : c) {
//         LiteralSet new_set;
//         new_set.insert(a_set.begin(), a_set.end());
//         new_set.insert(b_set.begin(), b_set.end());
//         new_set.insert(c_set.begin(), c_set.end());
//         result.insert(new_set);
//       }
//     }
//   }
//   return result;
// }
void cartesian_product(const std::set<LiteralSet>& a, const std::set<LiteralSet>& b, const std::set<LiteralSet>& c,
                       const LiteralSet& explanation_to_add, std::set<LiteralSet>& destination) {
  const std::set<LiteralSet> empty_set{{}};
  const std::set<LiteralSet>& first = a.empty() ? empty_set : a;
  const std::set<LiteralSet>& second = b.empty() ? empty_set : b;
  const std::set<LiteralSet>& third = c.empty() ? empty_set : c;
  for (const auto& a_set : first) {
    for (const auto& b_set : second) {
      for (const auto& c_set : third) {
        LiteralSet new_set;
        new_set.insert(a_set.begin(), a_set.end());
        new_set.insert(b_set.begin(), b_set.end());
        new_set.insert(c_set.begin(), c_set.end());
        new_set.insert(explanation_to_add.begin(), explanation_to_add.end());
        destination.insert(new_set);
      }
    }
  }
}

bool check_explanation(const TheorySolverBoundPreprocessor& preprocessor, const std::set<LiteralSet>& explanations) {
  mpq_class zero{0};
  Config config = preprocessor.config();

  config.m_filename() = "";
  config.m_read_from_stdin() = false;
  config.m_disable_theory_preprocessor() = true;
  for (const auto& explanation : explanations) {
    Context smt_solver{config};
    for (const auto& [var, truth] : explanation) {
      const Formula f = truth ? preprocessor.predicate_abstractor()[var] : !preprocessor.predicate_abstractor()[var];
      for (const Variable& free : f.GetFreeVariables()) {
        smt_solver.DeclareVariable(free);
      }
      smt_solver.Assert(f);
    }
    const auto result = smt_solver.CheckSat(&zero);
    if (result != SatResult::SAT_UNSATISFIABLE) {
      DLINEAR_RUNTIME_ERROR_FMT("The explanation {} is not valid", explanation);
      return false;
    }
  }
  return true;
}
}  // namespace

TheorySolverBoundPreprocessor::TheorySolverBoundPreprocessor(const TheorySolver& theory_solver)
    : TheorySolverBoundPreprocessor{theory_solver.predicate_abstractor(), theory_solver.theory_col_to_var(),
                                    theory_solver.var_to_theory_col(),    theory_solver.theory_row_to_lit(),
                                    theory_solver.lit_to_theory_row(),    theory_solver.theory_bounds()} {}
TheorySolverBoundPreprocessor::TheorySolverBoundPreprocessor(const PredicateAbstractor& predicate_abstractor,
                                                             const std::vector<Variable>& theory_col_to_var,
                                                             const std::map<Variable::Id, int>& var_to_theory_cols,
                                                             const std::vector<Literal>& theory_row_to_var,
                                                             const std::map<Variable::Id, int>& lit_to_rows,
                                                             const TheorySolverBoundVectorVector& theory_bounds)
    : config_{predicate_abstractor.config()},
      predicate_abstractor_{predicate_abstractor},
      theory_cols_{theory_col_to_var},
      var_to_cols_{var_to_theory_cols},
      theory_rows_{theory_row_to_var},
      lit_to_rows_{lit_to_rows},
      theory_bounds_{theory_bounds} {}

bool TheorySolverBoundPreprocessor::AddConstraint(const int theory_row, const Formula& formula) {
  if (config_.disable_theory_preprocessor()) return false;
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::AddConstraint({}, {})", theory_row, formula);
  if (!ShouldPropagateEqBinomial(formula)) return false;
  const mpq_class coeff = ExtractEqBoundCoefficient(formula);
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::AddConstraint: {}, coeff = {}", formula, coeff);
  row_to_eq_binomial_edge_coefficients_.emplace(theory_row, coeff);
  return true;
}

TheorySolverBoundPreprocessor::Explanations TheorySolverBoundPreprocessor::Process(
    const std::vector<int>& enabled_theory_rows) {
  Explanations explanations;
  Process(enabled_theory_rows, explanations);
  return explanations;
}
void TheorySolverBoundPreprocessor::Process(const std::vector<int>& enabled_theory_rows, Explanations& explanations) {
  if (config_.disable_theory_preprocessor()) return;
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::Process({})", enabled_theory_rows);
  SetEnvironmentFromBounds();
  PropagateConstraints(enabled_theory_rows, explanations);
  DLINEAR_WARN_FMT("TheorySolverBoundPreprocessor::Process:{} conflict found during propagation",
                   explanations.empty() ? " no" : "");
  DLINEAR_ASSERT(check_explanation(*this, explanations), "All explanations must be valid");
  if (!explanations.empty()) return;
  EvaluateFormulas(enabled_theory_rows, explanations);
  DLINEAR_WARN_FMT("TheorySolverBoundPreprocessor::Process:{} conflict found during evaluation",
                   explanations.empty() ? " no" : "");
}

void TheorySolverBoundPreprocessor::Clear() {
  env_ = Environment{};
  graph_.ClearEdges();
}

void TheorySolverBoundPreprocessor::SetEnvironmentFromBounds() {
  DLINEAR_ASSERT(theory_bounds_.size() >= theory_cols_.size(), "The number of bounds must be >= the number of columns");
  for (size_t theory_col = 0; theory_col < theory_cols_.size(); theory_col++) {
    const TheorySolverBoundVector& bound = theory_bounds_[theory_col];
    const mpq_class* const active_bound = bound.GetActiveEqualityBound();
    if (active_bound == nullptr) continue;
    const Variable& var = theory_cols_[theory_col];
    env_[var] = *active_bound;
  }
}

bool TheorySolverBoundPreprocessor::PropagateEqBinomial(const int theory_row, Explanations& explanations) {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::PropagateEqBinomial({})", theory_row);

  const mpq_class& coeff = row_to_eq_binomial_edge_coefficients_.at(theory_row);
  const auto& [from, to] = ExtractBoundEdge(predicate_abstractor_[theory_rows_[theory_row].var]);

  Environment::const_iterator updater_it;
  Variable to_update_variable;
  mpq_class new_value;
  if ((updater_it = env_.find(from)) != env_.end()) {
    DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::PropagateEqBinomial: {} --{} --> {}", to, theory_row, from);
    new_value = updater_it->second * coeff;
    to_update_variable = to;
  } else if ((updater_it = env_.find(to)) != env_.end()) {
    DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::PropagateEqBinomial: {} --{} --> {}", from, theory_row, to);
    new_value = updater_it->second / coeff;
    to_update_variable = from;
  } else {
    // Neither of the two variables is in the environment. Can't propagate
    return false;
  }

  auto to_update_it = env_.find(to_update_variable);
  // The value was still not in the environment. Propagate it
  if (to_update_it == env_.end()) {
    const auto [updated_it, inserted] = env_.insert(to_update_variable, new_value);
    DLINEAR_ASSERT(inserted, "The value must have been inserted");
    to_update_it = updated_it;
  } else if (to_update_it->second != new_value) {  // The value conflicts with the one already in the environment
    fmt::print("Conflict between {} and {}\n", to_update_it->first, updater_it->first);
    fmt::print("Value: {} != {}\n", to_update_it->second, new_value);
    // Conflict between to previously disconnected variables
    AddPathsToExplanations(to_update_it->first, updater_it->first, theory_rows_.at(theory_row), explanations);
    return true;
  }

  graph_.AddEdge(to_update_it->first, updater_it->first, theory_row, false);
  return true;
}

void TheorySolverBoundPreprocessor::PropagateConstraints(const std::vector<int>& enabled_theory_rows,
                                                         Explanations& explanations) {
  DLINEAR_TRACE("TheorySolverBoundPreprocessor::PropagateConstraints()");
  std::list<int> candidate_rows{enabled_theory_rows.cbegin(), enabled_theory_rows.cend()};

  // Remove all rows that have only one free variable, since they can't be propagated
  candidate_rows.remove_if([this](const int theory_row) {
    return predicate_abstractor_[theory_rows_[theory_row].var].GetFreeVariables().size() <= 1;
  });

  bool continue_propagating;
  // While we still have constraints to propagate...
  do {
    continue_propagating = false;
    for (auto it = candidate_rows.begin(); it != candidate_rows.end();) {
      const int theory_row = *it;
      const Literal& lit = theory_rows_.at(theory_row);
      // Simple binomial equality. Handle it more efficiently
      if (ShouldPropagateEqBinomial(lit)) {
        if (PropagateEqBinomial(theory_row, explanations)) {
          continue_propagating = true;
          it = candidate_rows.erase(it);
        } else {
          ++it;
        }
        continue;
      }
      // Not a row we can propagate at the moment
      if (!ShouldPropagateRows(lit)) {
        ++it;
        continue;
      };
      continue_propagating = true;
      const Formula& formula = predicate_abstractor_[lit.var];
      DLINEAR_ASSERT(is_addition(get_lhs_expression(formula)), "lhs expression must be an addition");
      std::vector<Variable> dependencies;
      mpq_class rhs{get_constant_value(get_rhs_expression(formula))};
      mpq_class var_coeff{};
      Variable var_propagated{};
      for (const auto& [expr, coeff] : get_expr_to_coeff_map_in_addition(get_lhs_expression(formula))) {
        DLINEAR_ASSERT(is_variable(expr), "All expressions in lhs formula must be variables");
        const Variable& var = get_variable(expr);
        const auto env_it = env_.find(var);
        if (env_it != env_.cend()) {
          rhs -= env_it->second * coeff;
          dependencies.emplace_back(var);
        } else {
          var_propagated = var;
          var_coeff = coeff;
        }
      }
      DLINEAR_ASSERT(!var_propagated.is_dummy(), "There must be exactly a propagated variable");
      DLINEAR_ASSERT(var_coeff != 0, "The propagated variable coefficient cannot be 0");

      // Calculate the propagated value of the variable
      rhs /= var_coeff;
      // Add all the dependencies edges to the graph
      for (auto& to_var : dependencies) graph_.AddEdge(var_propagated, to_var, theory_row, false);
      env_[var_propagated] = rhs;
      DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::PropagateConstraints: {} = {} thanks to row {} and {}",
                        var_propagated, rhs, theory_row, dependencies);
      it = candidate_rows.erase(it);
    }
  } while (continue_propagating && explanations.empty());
}

void TheorySolverBoundPreprocessor::EvaluateFormulas(const std::vector<int>& enabled_theory_rows,
                                                     Explanations& explanations) {
  DLINEAR_ASSERT(explanations.empty(), "The explanations vector must be empty");
  DLINEAR_TRACE("TheorySolverBoundPreprocessor::EvaluateFormulas()");
  for (const auto& theory_row : enabled_theory_rows) {
    const Literal& lit = theory_rows_.at(theory_row);
    if (!ShouldEvaluate(lit)) continue;
    const Formula& formula = predicate_abstractor_[lit.var];
    const bool satisfied = formula.Evaluate(env_) == lit.truth;
    if (!satisfied) {
      DLINEAR_DEBUG_FMT("TheorySolverBoundPreprocessor::EvaluateFormulas: {} => FAIL", lit);
      FormulaViolationExplanation(lit, formula, explanations);
    }
  }
}

void TheorySolverBoundPreprocessor::FormulaViolationExplanation(const Literal& lit, const Formula& formula,
                                                                Explanations& explanations) {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::FormulaViolationExplanation({})", formula);
  // TODO: produce more than just one explanation! Produce as many as possible!
  LiteralSet explanation;
  explanation.insert(lit);
  for (const auto& var : formula.GetFreeVariables()) {
    DLINEAR_ASSERT(env_.find(var) != env_.end(), "All free variables must be in the environment");
    GetExplanation(var, explanation);
  }
  explanations.insert(explanation);
}

bool TheorySolverBoundPreprocessor::ShouldEvaluate(const Literal& lit) const {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldEvaluate({})", lit);
  // We already have checked this kind of formula when propagating the environment
  // While it wouldn't be an issue to do it again, it's more efficient to just do a quick check
  if (ShouldPropagateEqBinomial(lit)) return false;
  const auto& [var, truth] = lit;
  const Formula& formula = predicate_abstractor_[var];
  // No need to evaluate if there are no free variables
  if (formula.GetFreeVariables().empty()) return false;
  // TODO: no need to evaluate rows that have an equality bound already expressed
  // All free variables must be in the environment
  return std::all_of(formula.GetFreeVariables().begin(), formula.GetFreeVariables().end(),
                     [this](const Variable& v) { return env_.find(v) != env_.end(); });
}
bool TheorySolverBoundPreprocessor::ShouldEvaluate(const Formula& formula) const {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldEvaluate({})", formula);
  // We already have checked this kind of formula when propagating the environment
  // While it wouldn't be an issue to do it again, it's more efficient to just do a quick check
  if (ShouldPropagateEqBinomial(formula)) return false;
  // No need to evaluate if there are no free variables
  if (formula.GetFreeVariables().empty()) return false;
  // TODO: no need to evaluate rows that have an equality bound already expressed
  // All free variables must be in the environment
  return std::all_of(formula.GetFreeVariables().begin(), formula.GetFreeVariables().end(),
                     [this](const Variable& v) { return env_.find(v) != env_.end(); });
}

bool TheorySolverBoundPreprocessor::ShouldPropagateEqBinomial(const Literal& lit) const {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldPropagateEqBinomial({})", lit);
  const auto& [var, truth] = lit;
  const Formula& formula = predicate_abstractor_[var];
  // There must be exactly two free variables and an equality relation between them
  if (truth && !is_equal_to(formula)) return false;
  if (!truth && !is_not_equal_to(formula)) return false;
  return ShouldPropagateEqBinomial(formula);
}
bool TheorySolverBoundPreprocessor::ShouldPropagateEqBinomial(const Formula& formula) const {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldPropagateEqBinomial({})", formula);
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  // There must be exactly two free variables and an equality relation between them
  if (formula.GetFreeVariables().size() != 2) return false;
  if (!is_equal_to(formula) && !is_not_equal_to(formula)) return false;

  // The formula must be of the form 'ax == by', with a,b != 0
  const Expression& lhs = get_lhs_expression(formula);
  const Expression& rhs = get_rhs_expression(formula);
  if (!is_addition(lhs) || get_constant_value(rhs) != 0) return false;
  const auto& expr_to_coeff_map = to_addition(lhs)->get_expr_to_coeff_map();
  if (expr_to_coeff_map.size() != 2) return false;
  return is_variable(expr_to_coeff_map.cbegin()->first) && is_variable(std::next(expr_to_coeff_map.cbegin())->first) &&
         expr_to_coeff_map.cbegin()->second != 0 && std::next(expr_to_coeff_map.cbegin())->second != 0;
}

bool TheorySolverBoundPreprocessor::ShouldPropagateRows(const Literal& lit) {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldPropagateRows({})", lit);
  const auto& [var, truth] = lit;
  const Formula& formula = predicate_abstractor_[var];
  // There must be exactly two free variables and an equality relation between them
  if (truth && !is_equal_to(formula)) return false;
  if (!truth && !is_not_equal_to(formula)) return false;
  return ShouldPropagateRows(formula);
}
bool TheorySolverBoundPreprocessor::ShouldPropagateRows(const Formula& formula) {
  DLINEAR_TRACE_FMT("TheorySolverBoundPreprocessor::ShouldPropagateRows({})", formula);
  // There must be exactly two free variables and an equality relation between them
  if (!is_equal_to(formula) && !is_not_equal_to(formula)) return false;
  if (formula.GetFreeVariables().size() < 2) return false;
  DLINEAR_ASSERT(is_addition(get_lhs_expression(formula)), "lhs expression must be an addition");

  size_t missing_var_count{0};
  for (const auto& [expr, coeff] : get_expr_to_coeff_map_in_addition(get_lhs_expression(formula))) {
    DLINEAR_ASSERT(is_variable(expr), "All expressions in lhs formula must be variables");
    if (env_.find(get_variable(expr)) != env_.cend()) continue;
    if (++missing_var_count > 1) return false;
  }
  return missing_var_count == 1;
}

std::pair<Variable, Variable> TheorySolverBoundPreprocessor::ExtractBoundEdge(const Formula& formula) const {
  DLINEAR_ASSERT(is_equal_to(formula), "Formula should be an equality relation");
  DLINEAR_ASSERT(formula.GetFreeVariables().size() == 2, "Formula should have exactly two free variables");
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  const Expression& lhs = get_lhs_expression(formula);

  const std::map<Expression, mpq_class>& map = get_expr_to_coeff_map_in_addition(lhs);
  DLINEAR_ASSERT(map.size() == 2, "Expression should have exactly two variables");
  DLINEAR_ASSERT(get_constant_value(get_rhs_expression(formula)) == 0, "The right-hand side must be 0");

  return {
      get_variable(map.cbegin()->first),             // From vertex (variable)
      get_variable(std::next(map.cbegin())->first),  // To vertex (variable)
  };
}

mpq_class TheorySolverBoundPreprocessor::ExtractEqBoundCoefficient(const Formula& formula) const {
  DLINEAR_ASSERT(is_equal_to(formula), "Formula should be an equality relation");
  DLINEAR_ASSERT(formula.GetFreeVariables().size() == 2, "Formula should have exactly two free variables");
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  const Expression& lhs = get_lhs_expression(formula);

  const std::map<Expression, mpq_class>& map = get_expr_to_coeff_map_in_addition(lhs);
  DLINEAR_ASSERT(map.size() == 2, "Expression should have exactly two variables");
  DLINEAR_ASSERT(get_constant_value(get_rhs_expression(formula)) == 0, "The right-hand side must be 0");

  return -(std::next(map.cbegin())->second) / map.cbegin()->second;
}

void TheorySolverBoundPreprocessor::AddPathsToExplanations(const Variable& from, const Variable& to,
                                                           const Literal& conflicting_literal,
                                                           TheorySolverBoundPreprocessor::Explanations& explanations) {
  const std::vector<Variable> from_origins = GetExplanationOrigins(from);
  const std::vector<Variable> to_origins = GetExplanationOrigins(to);
  fmt::print("From {}\nTo{}\n", from_origins, to_origins);
  for (const Variable& from_origin : from_origins) {
    for (const Variable& to_origin : to_origins) {
      fmt::print("{} --> {}\n", from_origin, to_origin);
      std::set<LiteralSet> from_explanations;
      std::set<LiteralSet> from_to_explanations;
      std::set<LiteralSet> to_explanations;
      LiteralSet base_explanation{conflicting_literal};
      const TheorySolverBoundVector& from_bounds = theory_bounds_.at(var_to_cols_.at(from_origin.get_id()));
      const TheorySolverBoundVector& to_bounds = theory_bounds_.at(var_to_cols_.at(to_origin.get_id()));
      from_bounds.GetActiveExplanation(theory_rows_, base_explanation);
      to_bounds.GetActiveExplanation(theory_rows_, base_explanation);

      DLINEAR_ASSERT(from_bounds.GetActiveEqualityBound() != nullptr, "The starting variable must have an eq bound");
      DLINEAR_ASSERT(to_bounds.GetActiveEqualityBound() != nullptr, "The ending variable must have an eq bound");

      // Insert all rows from the edges in the path to the explanation
      graph_.AllPaths(from, from_origin, [&](std::vector<Variable>& path) {
        LiteralSet explanation;
        for (size_t i = 1; i < path.size(); i++) {
          DLINEAR_ASSERT(graph_.GetEdgeWeight(path[i - 1], path[i]) != nullptr, "Edge must exist");
          const int theory_row = *graph_.GetEdgeWeight(path[i - 1], path[i]);
          explanation.insert(theory_rows_[theory_row]);
        }
        fmt::print("AllPaths1: {}\n", explanation);
        from_explanations.insert(explanation);
        return VisitResult::CONTINUE;
      });
      graph_.AllPaths(from, to, [&](std::vector<Variable>& path) {
        // Insert all rows from the edges in the path to the explanation
        LiteralSet explanation;
        for (size_t i = 1; i < path.size(); i++) {
          DLINEAR_ASSERT(graph_.GetEdgeWeight(path[i - 1], path[i]) != nullptr, "Edge must exist");
          const int theory_row = *graph_.GetEdgeWeight(path[i - 1], path[i]);
          explanation.insert(theory_rows_[theory_row]);
        }
        fmt::print("AllPaths2: {}\n", explanation);
        from_to_explanations.insert(explanation);
        return VisitResult::CONTINUE;
      });
      graph_.AllPaths(to, to_origin, [&](std::vector<Variable>& path) {
        // Insert all rows from the edges in the path to the explanation
        LiteralSet explanation;
        for (size_t i = 1; i < path.size(); i++) {
          DLINEAR_ASSERT(graph_.GetEdgeWeight(path[i - 1], path[i]) != nullptr, "Edge must exist");
          const int theory_row = *graph_.GetEdgeWeight(path[i - 1], path[i]);
          explanation.insert(theory_rows_[theory_row]);
        }
        fmt::print("AllPaths3: {}\n", explanation);
        to_explanations.insert(explanation);
        return VisitResult::CONTINUE;
      });
      cartesian_product(from_explanations, from_to_explanations, to_explanations, base_explanation, explanations);
      fmt::print("Explanations {}\n", explanations);
    }
  }
}

void TheorySolverBoundPreprocessor::AddPathToExplanation(const Variable& from, const Variable& to,
                                                         LiteralSet& explanation) {
  const TheorySolverBoundVector& from_bounds = theory_bounds_.at(var_to_cols_.at(from.get_id()));
  const TheorySolverBoundVector& to_bounds = theory_bounds_.at(var_to_cols_.at(to.get_id()));
  AddPathToExplanation(from, to, from_bounds, to_bounds, explanation);
}
void TheorySolverBoundPreprocessor::AddPathToExplanation(const Variable& from, const Variable& to,
                                                         const TheorySolverBoundVector& from_bounds,
                                                         const TheorySolverBoundVector& to_bounds,
                                                         LiteralSet& explanation) {
  graph_.AllPaths(from, to, [&](std::vector<Variable>& path) {
    DLINEAR_ASSERT_FMT(to_bounds.GetActiveEqualityBound() != nullptr, "The ending variable {} must have an eq bound",
                       to);
    // Insert start and end bounds to the explanation
    if (from_bounds.GetActiveEqualityBound() != nullptr) from_bounds.GetActiveEqExplanation(theory_rows_, explanation);
    to_bounds.GetActiveEqExplanation(theory_rows_, explanation);
    // Insert all rows from the edges in the path to the explanation
    for (size_t i = 1; i < path.size(); i++) {
      DLINEAR_ASSERT(graph_.GetEdgeWeight(path[i - 1], path[i]) != nullptr, "Edge must exist");
      const int theory_row = *graph_.GetEdgeWeight(path[i - 1], path[i]);
      explanation.insert(theory_rows_[theory_row]);
    }
    return VisitResult::STOP;
  });
}

void TheorySolverBoundPreprocessor::GetExplanation(const Variable& var, LiteralSet& explanation) {
  const TheorySolverBoundVector& bounds = theory_bounds_.at(var_to_cols_.at(var.get_id()));
  // If the variable has its bounds set directly by some literals, simply add them to the explanation
  if (bounds.GetActiveEqualityBound() != nullptr) {
    bounds.GetActiveExplanation(theory_rows_, explanation);
  } else {  // else we need to find the variable responsible for the bound propagation from the bound_graph
    graph_.BFS(var, [&](const Variable& from, const Variable& to, const Weight&) {
      if (to.equal_to(from)) return VisitResult::CONTINUE;
      const TheorySolverBoundVector& to_bounds = theory_bounds_.at(var_to_cols_.at(to.get_id()));
      if (to_bounds.GetActiveEqualityBound() == nullptr) return VisitResult::CONTINUE;
      AddPathToExplanation(var, to, bounds, to_bounds, explanation);
      return VisitResult::STOP;
    });
  }
}

std::vector<Variable> TheorySolverBoundPreprocessor::GetExplanationOrigins(const Variable& var) {
  const TheorySolverBoundVector& bounds = theory_bounds_.at(var_to_cols_.at(var.get_id()));
  // If the variable has its bounds set directly by some literals, it is its own origin
  if (bounds.GetActiveEqualityBound() != nullptr) {
    return {var};
  }
  // We need to find the variable responsible for the bound propagation from the bound_graph
  std::vector<Variable> origins;
  graph_.BFS(var, [&](const Variable& from, const Variable& to, const Weight&) {
    if (to.equal_to(from)) return VisitResult::CONTINUE;
    const TheorySolverBoundVector& to_bounds = theory_bounds_.at(var_to_cols_.at(to.get_id()));
    if (to_bounds.GetActiveEqualityBound() == nullptr) return VisitResult::CONTINUE;
    origins.emplace_back(to);
    return VisitResult::SKIP;
  });
  DLINEAR_ASSERT(!origins.empty(), "There must be at least one origin");
  return origins;
}

std::ostream& operator<<(std::ostream& os, const TheorySolverBoundPreprocessor& preprocessor) {
  return os << "TheorySolverBoundPreprocessor{" << "env_ = " << preprocessor.env() << ", "
            << "theory_cols_ = " << preprocessor.theory_cols() << ", "
            << "theory_rows_ = " << preprocessor.theory_rows() << ", "
            << "theory_bounds_ = " << preprocessor.theory_bounds() << ", " << "graph_ = " << preprocessor.bound_graph()
            << "}";
}

}  // namespace dlinear
