/**
 * @file PlaistedGreenbaumCnfizer.cpp
 * @author dlinear
 * @date 18 Aug 2023
 * @copyright 2023 dlinear
 */

#include "dlinear/symbolic/PlaistedGreenbaumCnfizer.h"

using std::cout;
using std::to_string;
using std::vector;
using std::set;
using std::string;

namespace dlinear {

namespace {
// A class to show statistics information at destruction.
class PlaistedGreenbaumCnfizerStat : public Stats {
 public:
  explicit PlaistedGreenbaumCnfizerStat(const bool enabled) : Stats{enabled} {}
  PlaistedGreenbaumCnfizerStat(const PlaistedGreenbaumCnfizerStat &) = delete;
  PlaistedGreenbaumCnfizerStat(PlaistedGreenbaumCnfizerStat &&) = delete;
  PlaistedGreenbaumCnfizerStat &operator=(const PlaistedGreenbaumCnfizerStat &) = delete;
  PlaistedGreenbaumCnfizerStat &operator=(PlaistedGreenbaumCnfizerStat &&) = delete;
  ~PlaistedGreenbaumCnfizerStat() override {
    if (enabled()) {
      using fmt::print;
      print(cout, "{:<45} @ {:<20} = {:>15}\n", "Total # of Convert",
            "PlaistedGreenbaum Cnfizer", num_convert_);
      if (num_convert_ > 0) {
        print(cout, "{:<45} @ {:<20} = {:>15f} sec\n",
              "Total time spent in Converting", "PlaistedGreenbaum Cnfizer",
              timer_convert_.seconds());
      }
    }
  }

  void increase_num_convert() { increase(&num_convert_); }

  Timer timer_convert_;

 private:
  std::atomic<int> num_convert_{0};
};
}  // namespace

vector <Formula> PlaistedGreenbaumCnfizer::Convert(const Formula &f) {
  static PlaistedGreenbaumCnfizerStat stat{DLINEAR_INFO_ENABLED};
  TimerGuard timer_guard(&stat.timer_convert_, stat.enabled());
  stat.increase_num_convert();
  // Put the Formula into negation normal form
  const Formula &g{nnfizer_.Convert(f, true /* push_negation_into_relationals */)};
  aux_.clear();
  vars_.clear();
  vector<Formula> ret;
  const Formula head{Visit(g)};
  aux_.push_back(head);
  return aux_;
}

Formula PlaistedGreenbaumCnfizer::Visit(const Formula &f) {
  // TODO(soonho): use cache.
  return VisitFormula<Formula>(this, f);
}

Formula PlaistedGreenbaumCnfizer::VisitForall(const Formula &f) {
  // We always need a variable
  static size_t id{0};
  const Variable bvar{string("forall") + to_string(id++), Variable::Type::BOOLEAN};
  vars_.push_back(bvar);

  // Given: f := ∀y. φ(x, y), this process CNFizes φ(x, y), pushes the
  // universal quantifier over conjunctions, and inserts ¬b:
  //
  //     = ∀y. (clause₁(x, y) ∧ ... ∧ clauseₙ(x, y))
  //     = (∀y. ¬b v clause₁(x, y)) ∧ ... ∧ (∀y. ¬b v clauseₙ(x, y))
  const Variables &quantified_variables{get_quantified_variables(f)};  // y
  const Formula &quantified_formula{get_quantified_formula(f)};  // φ(x, y)
  // clause₁(x, y) ∧ ... ∧ clauseₙ(x, y)
  const set<Formula> clauses{get_clauses(naive_cnfizer_.Convert(quantified_formula))};
  for (const Formula &clause : clauses) {
    set<Formula> new_clause_set{!bvar};
    if (is_disjunction(clause)) {
      DLINEAR_ASSERT(is_clause(clause), "Must be a clause");
      set<Formula> temp{get_operands(clause)};
      new_clause_set.insert(temp.begin(), temp.end());
    } else {
      new_clause_set.insert(clause);
    }
    Formula new_clause{make_disjunction(new_clause_set)};
    DLINEAR_ASSERT(is_clause(new_clause), "Must be a clause");
    // Only the old clause's variables can intersect
    if (HaveIntersection(clause.GetFreeVariables(), quantified_variables)) {
      aux_.emplace_back(forall(quantified_variables, new_clause));
    } else {
      aux_.emplace_back(new_clause);
    }
  }

  return Formula{bvar};
}

// TODO: flatten nested conjunctions and disjunctions?

Formula PlaistedGreenbaumCnfizer::VisitConjunction(const Formula &f) {
  static size_t id{0};
  // Introduce a new Boolean variable, `bvar` for `f`.
  const Variable bvar{string("conj") + to_string(id++),
                      Variable::Type::BOOLEAN};
  vars_.push_back(bvar);
  for (const Formula &op : get_operands(f)) {
    aux_.emplace_back(!bvar || this->Visit(op));
  }
  return Formula{bvar};
}

Formula PlaistedGreenbaumCnfizer::VisitDisjunction(const Formula &f) {
  static size_t id{0};
  // Introduce a new Boolean variable, `bvar` for `f`.
  const Variable bvar{string("disj") + to_string(id++),
                      Variable::Type::BOOLEAN};
  vars_.push_back(bvar);
  set<Formula> clause{::dlinear::map(
      get_operands(f),
      [this](const Formula &formula) { return this->Visit(formula); })};
  clause.insert(!bvar);
  aux_.emplace_back(make_disjunction(clause));
  return Formula{bvar};
}

Formula PlaistedGreenbaumCnfizer::VisitNegation(const Formula &f) {
  DLINEAR_ASSERT(is_atomic(get_operand(f)), "Must be atomic");
  return f;
}

} // namespace dlinear
