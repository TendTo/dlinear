/**
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "EqBinomialPreprocessor.h"

#include <unordered_set>

#include "QfLraTheorySolver.h"
#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/theory_solver/TheorySolver.h"
#include "dlinear/util/error.h"

namespace dlinear {

EqBinomialPreprocessor::EqBinomialPreprocessor(const TheorySolver& theory_solver,
                                               const std::shared_ptr<BoundVectorMap>& var_bounds,
                                               const std::shared_ptr<Environment>& env, const std::string& class_name)
    : TheoryPreprocessor{theory_solver, class_name}, var_bounds_{var_bounds}, env_{env}, graph_{} {
  DLINEAR_ASSERT(var_bounds_ != nullptr, "The var_bounds must not be null");
  DLINEAR_ASSERT(env_ != nullptr, "The env must not be null");
}

Config::ExecutionStep EqBinomialPreprocessor::run_on_step() const {
  return theory_solver_.config().actual_eq_binomial_preprocess_step();
}

bool EqBinomialPreprocessor::EnableLiteral(const Literal& lit, const ConflictCallback& conflict_cb) {
  DLINEAR_TRACE_FMT("EqBinomialBoundPreprocessor::EnableConstraint({})", lit);
  // If the literal does not represent an equality relation, skip
  if (!ShouldPropagateBounds(lit)) return true;
  // Add the edge to the bound_graph  const Edge edge = ExtractBoundEdge(lit);
  auto [from, to, value] = ExtractBoundEdge(lit);
  DLINEAR_TRACE_FMT("EqBinomialBoundPreprocessor::EnableConstraint: adding {} --{}--> {}", from, value, to);

  // Check whether the edge already exists in the graph. If it does, check for conflicts, and if there are none, skip
  const EdgeValue* existing_edge_value = graph_.GetEdgeWeight(from, to);
  if (existing_edge_value != nullptr) {
    if (*existing_edge_value->rhs != *value.rhs) {  // Different rhs
      // Same coefficients. Conflict detected between the two literals
      if (*existing_edge_value->c_from == *value.c_from && *existing_edge_value->c_to == *value.c_to) {
        conflict_cb({existing_edge_value->lit, lit});
        return false;
      }
    }
    return true;  // Cannot add the edge as it already exists, but no conflict
  }
  [[maybe_unused]] bool conflicting_edge = graph_.AddEdge(from, to, value, false);
  DLINEAR_ASSERT(!conflicting_edge, "The edge should not conflict with any other edge");

  // Add the return edge, by inverting from and to coefficients
  std::swap(value.c_from, value.c_to);
  conflicting_edge |= graph_.AddEdge(to, from, value, false);
  DLINEAR_ASSERT(!conflicting_edge, "The edge should not conflict with any other edge");
  return true;
}

bool EqBinomialPreprocessor::ProcessCore(const ConflictCallback& conflict_cb) {
  DLINEAR_TRACE("EqBinomialBoundPreprocessor::Process()");
  // Sync the local var bounds with the ones from the theory solver if it is still empty
  if (var_bounds_->empty()) *var_bounds_ = static_cast<const QfLraTheorySolver&>(theory_solver_).vars_bounds();
  // Sync the environment with the active equality bounds from the var bounds if it is still empty
  if (env_->empty()) SetEnvironmentFromBounds();
  const bool no_conflict = PropagateEnvironment(conflict_cb);
  DLINEAR_DEBUG_FMT("EqBinomialBoundPreprocessor::Process no conflict found -> {}", no_conflict);
  return no_conflict;
}

void EqBinomialPreprocessor::Backtrack() {
  if (!env_->empty()) *env_ = Environment{};
  var_bounds_->clear();
  graph_.ClearEdges();
}

void EqBinomialPreprocessor::SetEnvironmentFromBounds() {
  for (const auto& [var, bound] : *var_bounds_) {
    const mpq_class* const active_bound = bound.GetActiveEqualityBound();
    if (active_bound == nullptr) continue;
    if (env_->contains(var)) {
      DLINEAR_ASSERT(env_->at(var) == *active_bound, "No conflict should arise from this assignment");
      continue;
    }
    (*env_)[var] = *active_bound;
  }
}

bool EqBinomialPreprocessor::PropagateEnvironment(const ConflictCallback& conflict_cb) {
  DLINEAR_TRACE("EqBinomialBoundPreprocessor::PropagateEnvironment: start propagation");
  bool no_conflict = true;
  const std::vector<std::pair<Variable, mpq_class>> vars_in_env{env_->begin(), env_->end()};
  for (const auto& [start_var, start_value] : vars_in_env) {
    graph_.BFS(start_var, [&](const Variable& from, const Variable& to, const EdgeValue& c) {
      DLINEAR_TRACE_FMT("EqBinomialBoundPreprocessor::PropagateEnvironment: from = {}, to = {}, c = {}", from, to, c);
      if (to.equal_to(from)) return VisitResult::CONTINUE;
      // If we are coming off one of the starting edge, we can remove it from the graph,
      // since it will check against every other edge in the graph
      if (from.equal_to(to)) graph_.RemoveEdge(to, from, false);
      DLINEAR_ASSERT(env_->find(from) != env_->end(), "The 'from' var must be in the environment");
      DLINEAR_ASSERT(var_bounds_->at(from).GetActiveEqualityBound() != nullptr, "The 'from' var must have an eq bound");
      DLINEAR_ASSERT(c.c_from != nullptr && c.c_to != nullptr && c.rhs != nullptr, "The pointers are not null");
      DLINEAR_ASSERT(*c.c_to != 0, "The 'to' coefficient must be non-zero");

      const BoundVector& from_bounds = var_bounds_->at(from);
      BoundVector& to_bounds = var_bounds_->at(to);

      const mpq_class new_to_value = (-env_->at(from) * *c.c_from + *c.rhs) / *c.c_to;
      Bound new_bound = {&new_to_value, LpColBound::B, c.lit};
      bool set_env = false;

      if (const auto it = env_->find(to); it == env_->end()) {
        // The 'to' variables was not assigned any values before, propagate it along with the explanation
        DLINEAR_TRACE_FMT("EqBinomialBoundPreprocessor::PropagateEnvironment: propagate {} = {}", to, new_to_value);
        (*env_)[to] = new_to_value;
        new_bound.value = &env_->at(to);
        set_env = true;
      } else if (it->second == new_to_value) {
        // There is no need to propagate this bound further. The 'to' node has a compatible eq bound already set.
        DLINEAR_ASSERT(to_bounds.GetActiveEqualityBound() != nullptr, "The 'to' var must have an active eq bound");
        return VisitResult::SKIP;
      }

      new_bound.explanation = from_bounds.GetActiveExplanation();

      const bool add_bound_no_conflict = to_bounds.AddBound(new_bound, conflict_cb);
      DLINEAR_ASSERT(!add_bound_no_conflict || env_->at(to) == new_to_value, "No conflict => env[to] == new_value");

      // If a conflict was detected, remove the returning edge to avoid re-discovering the same conflict.
      // Note that this approach may lead to missing some conflicts, but it is more efficient.
      if (!add_bound_no_conflict) {
        DLINEAR_DEBUG_FMT("EqBinomialBoundPreprocessor::PropagateEnvironment conflict: {} = {} => {}", from, c.lit, to);
        DLINEAR_TRACE_FMT("EqBinomialBoundPreprocessor::PropagateEnvironment conflict {}, {}", from_bounds, to_bounds);
        graph_.RemoveEdge(to, from, false);
        // Furthermore, if the value in the environment was set by this edge, remove it
        if (set_env) env_->erase(to);
      }
      no_conflict &= add_bound_no_conflict;
      return add_bound_no_conflict ? VisitResult::CONTINUE : VisitResult::SKIP;
    });
  }
  return no_conflict;
}

bool EqBinomialPreprocessor::ShouldPropagateBounds(const Literal& lit) const {
  DLINEAR_TRACE_FMT("EqBinomialBoundPreprocessor::ShouldPropagateBounds({})", lit);
  const auto& [var, truth] = lit;
  const Formula& formula = theory_solver_.predicate_abstractor()[var];
  // There must be exactly two free variables and an equality relation between them
  if (truth && !is_equal_to(formula)) return false;
  if (!truth && !is_not_equal_to(formula)) return false;
  return ShouldPropagateBounds(formula);
}
bool EqBinomialPreprocessor::ShouldPropagateBounds(const Formula& formula) const {
  DLINEAR_TRACE_FMT("EqBinomialBoundPreprocessor::ShouldPropagateBounds({})", formula);
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  // There must be exactly two free variables and an equality relation between them
  if (formula.GetFreeVariables().size() != 2) return false;
  if (!is_equal_to(formula) && !is_not_equal_to(formula)) return false;

  // The formula must be of the form 'ax == by', with a,b != 0
  const Expression& lhs = get_lhs_expression(formula);
  const Expression& rhs = get_rhs_expression(formula);
  DLINEAR_ASSERT(is_addition(lhs) && is_constant(rhs), "lhs must be an addition and rhs must be a constant");

  const auto& expr_to_coeff_map = to_addition(lhs)->get_expr_to_coeff_map();
  DLINEAR_ASSERT(expr_to_coeff_map.size() == 2u, "If the formula has two variables, there must be two coefficients");
  return is_variable(expr_to_coeff_map.cbegin()->first) && is_variable(std::next(expr_to_coeff_map.cbegin())->first) &&
         expr_to_coeff_map.cbegin()->second != 0 && std::next(expr_to_coeff_map.cbegin())->second != 0;
}

EqBinomialPreprocessor::Edge EqBinomialPreprocessor::ExtractBoundEdge(const Literal& lit) const {
  const Formula& formula = theory_solver_.predicate_abstractor()[lit.var];
  // DLINEAR_ASSERT(IsEqualTo(formula, lit.truth), "Formula should be an equality relation");
  DLINEAR_ASSERT(is_equal_to(formula), "Formula should be an equality relation");
  DLINEAR_ASSERT(formula.GetFreeVariables().size() == 2, "Formula should have exactly two free variables");
  DLINEAR_ASSERT(formula.IsFlattened(), "The formula must be flattened");
  const Expression& lhs = get_lhs_expression(formula);

  const std::map<Expression, mpq_class>& map = get_expr_to_coeff_map_in_addition(lhs);
  const mpq_class& rhs = get_constant_value(get_rhs_expression(formula));
  DLINEAR_ASSERT(map.size() == 2, "Expression should have exactly two variables");

  return {get_variable(map.cbegin()->first),             // From vertex (variable)
          get_variable(std::next(map.cbegin())->first),  // To vertex (variable)
                                                         // Edge value: from coefficient, to coefficient, rhs, literal
          {&map.cbegin()->second, &std::next(map.cbegin())->second, &rhs, lit}};
}

std::ostream& operator<<(std::ostream& os, const EqBinomialPreprocessor::EdgeValue& edge_value) {
  os << "EdgeValue{";
  if (edge_value.c_from != nullptr) os << "coefficient from = " << *edge_value.c_from << ", ";
  if (edge_value.c_to != nullptr) os << "coefficient to = " << *edge_value.c_to << ", ";
  if (edge_value.rhs != nullptr) os << "rhs = " << *edge_value.rhs << ", ";
  return os << "literal = " << edge_value.lit << "}";
}

std::ostream& operator<<(std::ostream& os, const EqBinomialPreprocessor::Edge& bound_edge) {
  return os << "BoundEdge{"
            << "from = " << bound_edge.from << ", "
            << "to = " << bound_edge.to << ", "
            << "value = " << bound_edge.value << "}";
}

std::ostream& operator<<(std::ostream& os, const EqBinomialPreprocessor& preprocessor) {
  return os << "EqBinomialBoundPreprocessor{"
            << "env_ = " << preprocessor.env() << ", "
            << "graph_ = " << preprocessor.graph() << "}";
}

}  // namespace dlinear
