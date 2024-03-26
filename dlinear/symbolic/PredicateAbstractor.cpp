/**
 * @file PredicateAbstractor.cpp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 */

#include "PredicateAbstractor.h"

#include "dlinear/symbolic/LinearFormulaFlattener.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/logging.h"

namespace dlinear {

void PredicateAbstractor::Add(const Variable &var, const Formula &f) {
  var_to_formula_map_.emplace(var, f);
  formula_to_var_map_.emplace(f, var);
}

Formula PredicateAbstractor::Convert(const Formula &f) {
  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();
  return Visit(f);
}

Formula PredicateAbstractor::Convert(const std::vector<Formula> &formulas) {
  return Convert(make_conjunction(std::set<Formula>{formulas.begin(), formulas.end()}));
}

Formula PredicateAbstractor::Visit(const Formula &f) {
  // First check if we processed this formula before.
  const auto it = formula_to_var_map_.find(f);
  if (it == formula_to_var_map_.cend()) {
    // No, we haven't processed it before.
    return VisitFormula<Formula>(this, f);
  } else {
    // Yes, we have processed this formula before.
    return Formula{it->second};
  }
}

Formula PredicateAbstractor::VisitAtomic(const Formula &f) {
  // Flatten linear formulas to make sure they have the standard form (ax + by <=> c).
  const Formula &flattened_f = flattener_.Flatten(f);
  auto it = formula_to_var_map_.find(flattened_f);
  // Leaf case: create a new Boolean variable `bvar` and record the relation between `bvar` and `f`.
  if (it == formula_to_var_map_.end()) {
    const Variable bvar{(std::stringstream{} << "b(" << f << ")").str(), Variable::Type::BOOLEAN};
    Add(bvar, flattened_f);
    return Formula{bvar};
  } else {
    return Formula{it->second};
  }
}

Formula PredicateAbstractor::VisitEqualTo(const Formula &f) { return VisitAtomic(f); }

Formula PredicateAbstractor::VisitNotEqualTo(const Formula &f) {
  const Expression &lhs{get_lhs_expression(f)};
  const Expression &rhs{get_rhs_expression(f)};
  return !VisitAtomic(lhs == rhs);
}

Formula PredicateAbstractor::VisitGreaterThan(const Formula &f) {
  const Expression &lhs{get_lhs_expression(f)};
  const Expression &rhs{get_rhs_expression(f)};
  return !VisitAtomic(lhs <= rhs);
}

Formula PredicateAbstractor::VisitGreaterThanOrEqualTo(const Formula &f) {
  const Expression &lhs{get_lhs_expression(f)};
  const Expression &rhs{get_rhs_expression(f)};
  return !VisitAtomic(lhs < rhs);
}

Formula PredicateAbstractor::VisitLessThan(const Formula &f) { return VisitAtomic(f); }

Formula PredicateAbstractor::VisitLessThanOrEqualTo(const Formula &f) { return VisitAtomic(f); }

Formula PredicateAbstractor::VisitConjunction(const Formula &f) {
  const std::set<Formula> operands{
      map(get_operands(f), [this](const Formula &formula) { return this->Visit(formula); })};
  return make_conjunction(operands);
}

Formula PredicateAbstractor::VisitDisjunction(const Formula &f) {
  const std::set<Formula> operands{
      map(get_operands(f), [this](const Formula &formula) { return this->Visit(formula); })};
  return make_disjunction(operands);
}

Formula PredicateAbstractor::VisitNegation(const Formula &f) { return !Visit(get_operand(f)); }

Formula PredicateAbstractor::VisitForall(const Formula &f) { return VisitAtomic(f); }

}  // namespace dlinear
