/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "PlaistedGreenbaumCnfizer.h"

#include <cstddef>
#include <set>
#include <string>

#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"

namespace dlinear {
std::pair<std::vector<Formula>, std::vector<Variable>> PlaistedGreenbaumCnfizer::Process(const Formula &f) const {
  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();
  // Put the Formula into negation normal form
  const Formula &g{nnfizer_.Process(f, true /* push_negation_into_relationals */)};
  std::vector<Formula> aux;
  std::vector<Variable> vars;
  const Formula head{VisitFormula(g, aux, vars)};
  aux.push_back(head);
  return {aux, vars};
}
std::pair<std::vector<Formula>, std::vector<Variable>> PlaistedGreenbaumCnfizer::operator()(const Formula &f) const {
  return Process(f);
}

Formula PlaistedGreenbaumCnfizer::VisitForall(const Formula &f, std::vector<Formula> &aux,
                                              std::vector<Variable> &vars) const {
  // We always need a variable
  static std::size_t id{0};
  const Variable bvar{std::string("forall") + std::to_string(id++), Variable::Type::BOOLEAN};
  vars.push_back(bvar);

  // Given: f := ∀y. φ(x, y), this process CNFizes φ(x, y), pushes the
  // universal quantifier over conjunctions, and inserts ¬b:
  //
  //     = ∀y. (clause₁(x, y) ∧ ... ∧ clauseₙ(x, y))
  //     = (∀y. ¬b v clause₁(x, y)) ∧ ... ∧ (∀y. ¬b v clauseₙ(x, y))
  const Variables &quantified_variables{get_quantified_variables(f)};  // y
  const Formula &quantified_formula{get_quantified_formula(f)};        // φ(x, y)
  // clause₁(x, y) ∧ ... ∧ clauseₙ(x, y)
  const std::set<Formula> clauses{get_clauses(naive_cnfizer_.Process(quantified_formula))};
  for (const Formula &clause : clauses) {
    std::set<Formula> new_clause_set{!bvar};
    if (is_disjunction(clause)) {
      DLINEAR_ASSERT(is_clause(clause), "Must be a clause");
      std::set<Formula> temp{get_operands(clause)};
      new_clause_set.insert(temp.begin(), temp.end());
    } else {
      new_clause_set.insert(clause);
    }
    Formula new_clause{make_disjunction(new_clause_set)};
    DLINEAR_ASSERT(is_clause(new_clause), "Must be a clause");
    // Only the old clause's variables can intersect
    if (HaveIntersection(clause.GetFreeVariables(), quantified_variables)) {
      aux.emplace_back(forall(quantified_variables, new_clause));
    } else {
      aux.emplace_back(new_clause);
    }
  }

  return Formula{bvar};
}

Formula PlaistedGreenbaumCnfizer::VisitConjunction(const Formula &f, std::vector<Formula> &aux,
                                                   std::vector<Variable> &vars) const {
  static std::size_t id{0};
  // Introduce a new Boolean variable, `bvar` for `f`.
  const Variable bvar{std::string("conj") + std::to_string(id++), Variable::Type::BOOLEAN};
  vars.push_back(bvar);
  for (const Formula &op : get_operands(f)) {
    aux.emplace_back(!bvar || VisitFormula(op, aux, vars));
  }
  return Formula{bvar};
}

Formula PlaistedGreenbaumCnfizer::VisitDisjunction(const Formula &f, std::vector<Formula> &aux,
                                                   std::vector<Variable> &vars) const {
  static std::size_t id{0};
  // Introduce a new Boolean variable, `bvar` for `f`.
  const Variable bvar{std::string("disj") + std::to_string(id++), Variable::Type::BOOLEAN};
  vars.push_back(bvar);
  std::set<Formula> clause{::dlinear::map(
      get_operands(f), [this, &aux, &vars](const Formula &formula) { return VisitFormula(formula, aux, vars); })};
  clause.insert(!bvar);
  aux.emplace_back(make_disjunction(clause));
  return Formula{bvar};
}

Formula PlaistedGreenbaumCnfizer::VisitNegation(const Formula &f, std::vector<Formula> &,
                                                std::vector<Variable> &) const {
  DLINEAR_ASSERT(is_atomic(get_operand(f)), "Must be atomic");
  return f;
}

}  // namespace dlinear
