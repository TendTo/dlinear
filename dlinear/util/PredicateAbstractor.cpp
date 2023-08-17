/**
 * @file PredicateAbstractor.cpp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */

#include "PredicateAbstractor.h"

using fmt::print;
using std::cout;
using std::stringstream;
using std::set;
using std::vector;

namespace dlinear {

/**
 * A class to show
 * statistics information
 * at destruction
 */
class PredicateAbstractorStat : public Stats {
 public:
  explicit PredicateAbstractorStat(const bool enabled) : Stats{enabled} {}
  PredicateAbstractorStat(const PredicateAbstractorStat &) = delete;
  PredicateAbstractorStat(PredicateAbstractorStat &&) = delete;
  PredicateAbstractorStat &operator=(const PredicateAbstractorStat &) = delete;
  PredicateAbstractorStat &operator=(PredicateAbstractorStat &&) = delete;
  ~PredicateAbstractorStat() override {
    if (enabled()) {
      print(cout, "{:<45} @ {:<20} = {:>15}\n", "Total # of Convert", "Predicate Abstractor", num_convert_);
      if (num_convert_ > 0) {
        print(cout,
              "{:<45} @ {:<20} = {:>15f} sec\n",
              "Total time spent in Converting",
              "Predicate Abstractor",
              timer_convert_.seconds());
      }
    }
  }

  void increase_num_convert() { increase(&num_convert_); }

  Timer timer_convert_;

 private:
  std::atomic<int> num_convert_{0};
};

void PredicateAbstractor::Add(const Variable &var, const Formula &f) {
  var_to_formula_map_.emplace(var, f);
  formula_to_var_map_.emplace(f, var);
}

Formula PredicateAbstractor::Convert(const Formula &f) {
  static PredicateAbstractorStat stat{DLINEAR_INFO_ENABLED};
  TimerGuard timer_guard(&stat.timer_convert_, stat.enabled());
  stat.increase_num_convert();
  return Visit(f);
}

Formula PredicateAbstractor::Convert(const vector<Formula> &formulas) {
  return Convert(
      make_conjunction(set<Formula>{formulas.begin(), formulas.end()}));
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

Formula PredicateAbstractor::VisitFalse(const Formula &f) {
  // Do nothing.
  return f;
}

Formula PredicateAbstractor::VisitTrue(const Formula &f) {
  // Do nothing.
  return f;
}

Formula PredicateAbstractor::VisitVariable(const Formula &f) {
  // Nothing to do for Boolean variables.
  return f;
}

Formula PredicateAbstractor::VisitAtomic(const Formula &f) {
  // Leaf case: create a new Boolean variable `bvar` and record the
  // relation between `bvar` and `f`.
  stringstream ss;
  ss << "b(" << f << ")";
  auto it = formula_to_var_map_.find(f);
  if (it == formula_to_var_map_.end()) {
    const Variable bvar{ss.str(), Variable::Type::BOOLEAN};
    Add(bvar, f);
    return Formula{bvar};
  } else {
    return Formula{it->second};
  }
}

Formula PredicateAbstractor::VisitEqualTo(const Formula &f) {
  return VisitAtomic(f);
}

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

Formula PredicateAbstractor::VisitLessThan(const Formula &f) {
  return VisitAtomic(f);
}

Formula PredicateAbstractor::VisitLessThanOrEqualTo(const Formula &f) {
  return VisitAtomic(f);
}

Formula PredicateAbstractor::VisitConjunction(const Formula &f) {
  const set<Formula> operands{
      map(get_operands(f),
          [this](const Formula &formula) { return this->Visit(formula); })};
  return make_conjunction(operands);
}

Formula PredicateAbstractor::VisitDisjunction(const Formula &f) {
  const set<Formula> operands{
      map(get_operands(f),
          [this](const Formula &formula) { return this->Visit(formula); })};
  return make_disjunction(operands);
}

Formula PredicateAbstractor::VisitNegation(const Formula &f) {
  return !Visit(get_operand(f));
}

Formula PredicateAbstractor::VisitForall(const Formula &f) {
  return VisitAtomic(f);
}

} // namespace dlinear
