/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "PredicateAbstractor.h"

#include <set>
#include <sstream>
#include <utility>

#include "dlinear/symbolic/LinearFormulaFlattener.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"

namespace dlinear {

Formula PredicateAbstractor::Process(const Formula &f) {
  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();
  return VisitFormula(f);
}
Formula PredicateAbstractor::operator()(const Formula &f) { return Process(f); }

Formula PredicateAbstractor::Process(const std::vector<Formula> &formulas) {
  return Process(make_conjunction(std::set<Formula>{formulas.begin(), formulas.end()}));
}
Formula PredicateAbstractor::operator()(const std::vector<Formula> &formulas) { return Process(formulas); }

Formula PredicateAbstractor::VisitFormula(const Formula &f) const {
  const Formula flattened_f{flattener_.Flatten(f)};
  const bool is_negated = is_negation(flattened_f);
  const Formula &unary_f = is_negated ? get_operand(flattened_f) : flattened_f;

  // First check if we processed this formula before.
  const auto it = formula_to_var_map_.find(unary_f);
  if (it == formula_to_var_map_.cend()) {
    // No, we haven't processed it before.
    return FormulaVisitor::VisitFormula(flattened_f);
  } else {
    // Yes, we have processed this formula before.
    return is_negated ? !Formula{it->second} : Formula{it->second};
  }
}

Formula PredicateAbstractor::VisitAtomic(const Formula &f) const {
  // Flatten linear formulas to make sure they have the standard form (ax + by <=> c).
  const Formula flattened_f{flattener_.Flatten(f)};
  const bool is_negated = is_negation(flattened_f);
  const Formula &unary_f = is_negated ? get_operand(flattened_f) : flattened_f;

  auto it = formula_to_var_map_.find(unary_f);
  // Leaf case: create a new Boolean variable `bvar` and record the relation between `bvar` and `f`.
  if (it == formula_to_var_map_.end()) {
    const Variable bvar{(std::stringstream{} << "b(" << unary_f << ")").str(), Variable::Type::BOOLEAN};
    var_to_formula_map_.emplace(bvar, unary_f);
    formula_to_var_map_.emplace(unary_f, bvar);
    return is_negated ? !Formula{bvar} : Formula{bvar};
  }
  return is_negated ? !Formula{it->second} : Formula{it->second};
}

Formula PredicateAbstractor::VisitEqualTo(const Formula &f) const { return VisitAtomic(f); }
Formula PredicateAbstractor::VisitNotEqualTo(const Formula &f) const { return VisitAtomic(f); }
Formula PredicateAbstractor::VisitLessThan(const Formula &f) const { return VisitAtomic(f); }
Formula PredicateAbstractor::VisitLessThanOrEqualTo(const Formula &f) const { return VisitAtomic(f); }
Formula PredicateAbstractor::VisitGreaterThan(const Formula &f) const { return VisitAtomic(f); }
Formula PredicateAbstractor::VisitGreaterThanOrEqualTo(const Formula &f) const { return VisitAtomic(f); }

Formula PredicateAbstractor::VisitNegation(const Formula &f) const { return !VisitFormula(get_operand(f)); }
Formula PredicateAbstractor::VisitForall(const Formula &f) const { return VisitAtomic(f); }
Formula PredicateAbstractor::VisitConjunction(const Formula &f) const {
  const std::set<Formula> operands{
      map(get_operands(f), [this](const Formula &formula) { return VisitFormula(formula); })};
  return make_conjunction(operands);
}
Formula PredicateAbstractor::VisitDisjunction(const Formula &f) const {
  const std::set<Formula> operands{
      map(get_operands(f), [this](const Formula &formula) { return VisitFormula(formula); })};
  return make_disjunction(operands);
}

}  // namespace dlinear
