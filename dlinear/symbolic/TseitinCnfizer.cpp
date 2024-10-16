/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */

#include "TseitinCnfizer.h"

#include <algorithm>
#include <cstddef>
#include <iterator>
#include <set>
#include <string>
#include <utility>

#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"

namespace dlinear {

namespace {
// A class to show statistics information at destruction.

// Forward declarations for the helper functions.
void Cnfize(const Variable &b, const Formula &f, std::vector<Formula> *clauses);
void CnfizeNegation(const Variable &b, const Formula &f, std::vector<Formula> *clauses);
void CnfizeConjunction(const Variable &b, const Formula &f, std::vector<Formula> *clauses);
void CnfizeDisjunction(const Variable &b, const Formula &f, std::vector<Formula> *clauses);
}  // namespace

// The main function of the TseitinCnfizer:
//  - It visits each node and introduce a Boolean variable `b` for
//    each subterm `f`, and keep the relation `b ⇔ f`.
//  - Then it cnfizes each `b ⇔ f` and make a conjunction of them.
std::vector<Formula> TseitinCnfizer::Process(const Formula &f) const {
  const TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();

  std::map<Variable, Formula> map;
  std::vector<Formula> ret;
  const Formula head{VisitFormula(f, map)};
  if (map.empty()) {
    return {head};
  }
  for (auto const &p : map) {
    if (get_variable(head).equal_to(p.first)) {
      if (is_conjunction(p.second)) {
        const std::set<Formula> &conjuncts(get_operands(p.second));
        copy(conjuncts.begin(), conjuncts.end(), back_inserter(ret));
      } else {
        ret.push_back(p.second);
      }
    } else {
      Cnfize(p.first, p.second, &ret);
    }
  }
  return ret;
}
std::vector<Formula> TseitinCnfizer::operator()(const Formula &f) const { return Process(f); }

Formula TseitinCnfizer::VisitForall(const Formula &f, std::map<Variable, Formula> &map) const {
  // Given: f := ∀y. φ(x, y), this process CNFizes φ(x, y) and push the
  // universal quantifier over conjunctions:
  //
  //     = ∀y. (clause₁(x, y) ∧ ... ∧ clauseₙ(x, y))
  //     = (∀y. clause₁(x, y)) ∧ ... ∧ (∀y. clauseₙ(x, y))
  const Variables &quantified_variables{get_quantified_variables(f)};  // y
  const Formula &quantified_formula{get_quantified_formula(f)};        // φ(x, y)
  // clause₁(x, y) ∧ ... ∧ clauseₙ(x, y)
  const std::set<Formula> clauses{get_clauses(naive_cnfizer_.Process(quantified_formula))};
  const std::set<Formula> new_clauses{::dlinear::map(clauses, [&quantified_variables](const Formula &clause) {
    DLINEAR_ASSERT(is_clause(clause), "Must be a clause");
    if (HaveIntersection(clause.GetFreeVariables(), quantified_variables)) {
      return forall(quantified_variables, clause);
    } else {
      return clause;
    }
  })};

  DLINEAR_ASSERT(!new_clauses.empty(), "Clause must not be empty");
  if (new_clauses.size() == 1) {
    return *(new_clauses.begin());
  } else {
    static std::size_t id{0};
    const Variable bvar{std::string("forall") + std::to_string(id++), Variable::Type::BOOLEAN};
    map.emplace(bvar, make_conjunction(new_clauses));
    return Formula{bvar};
  }
}

Formula TseitinCnfizer::VisitConjunction(const Formula &f, std::map<Variable, Formula> &map) const {
  // Introduce a new Boolean variable, `bvar` for `f` and record the
  // relation `bvar ⇔ f`.
  static std::size_t id{0};
  const std::set<Formula> transformed_operands{::dlinear::map(
      get_operands(f), [this, &map](const Formula &formula) { return this->VisitFormula(formula, map); })};
  const Variable bvar{std::string("conj") + std::to_string(id++), Variable::Type::BOOLEAN};
  map.emplace(bvar, make_conjunction(transformed_operands));
  return Formula{bvar};
}

Formula TseitinCnfizer::VisitDisjunction(const Formula &f, std::map<Variable, Formula> &map) const {
  static std::size_t id{0};
  const std::set<Formula> &transformed_operands{::dlinear::map(
      get_operands(f), [this, &map](const Formula &formula) { return this->VisitFormula(formula, map); })};
  const Variable bvar{std::string("disj") + std::to_string(id++), Variable::Type::BOOLEAN};
  map.emplace(bvar, make_disjunction(transformed_operands));
  return Formula{bvar};
}

Formula TseitinCnfizer::VisitNegation(const Formula &f, std::map<Variable, Formula> &map) const {
  const Formula &operand{get_operand(f)};
  if (is_atomic(operand)) {
    return f;
  } else {
    const Variable bvar{"neg", Variable::Type::BOOLEAN};
    const Formula transformed_operand{VisitFormula(operand, map)};
    map.emplace(bvar, !transformed_operand);
    return Formula{bvar};
  }
}

namespace {
// Cnfize b ⇔ f and add it to @p clauses. It calls Cnfize<FormulaKind> using
// pattern-matching.
void Cnfize(const Variable &b, const Formula &f, std::vector<Formula> *clauses) {
  switch (f.get_kind()) {
    case FormulaKind::False:
      DLINEAR_UNREACHABLE();
    case FormulaKind::True:
      DLINEAR_UNREACHABLE();
    case FormulaKind::Var:
      DLINEAR_UNREACHABLE();
    case FormulaKind::Eq:
      DLINEAR_UNREACHABLE();
    case FormulaKind::Neq:
      DLINEAR_UNREACHABLE();
    case FormulaKind::Gt:
      DLINEAR_UNREACHABLE();
    case FormulaKind::Geq:
      DLINEAR_UNREACHABLE();
    case FormulaKind::Lt:
      DLINEAR_UNREACHABLE();
    case FormulaKind::Leq:
      DLINEAR_UNREACHABLE();
    case FormulaKind::Forall:
      DLINEAR_UNREACHABLE();
    case FormulaKind::And:
      return CnfizeConjunction(b, f, clauses);
    case FormulaKind::Or:
      return CnfizeDisjunction(b, f, clauses);
    case FormulaKind::Not:
      return CnfizeNegation(b, f, clauses);
  }
  DLINEAR_UNREACHABLE();
}

// Add f to clauses if f is not true.
void Add(const Formula &f, std::vector<Formula> *clauses) {
  if (!is_true(f)) {
    clauses->push_back(f);
  }
}

// Add f₁ ⇔ f₂ to clauses.
void AddIff(const Formula &f1, const Formula &f2, std::vector<Formula> *clauses) {
  Add(imply(f1, f2), clauses);
  Add(imply(f2, f1), clauses);
}

// Cnfize b ⇔ ¬b₁ using the following equalities and add to clauses:
//   b ⇔ ¬b₁
// = (b → ¬b₁) ∧ (¬b₁ → b)
// = (¬b ∨ ¬b₁) ∧ (b₁ ∨ b)   (✓CNF)
void CnfizeNegation(const Variable &b, const Formula &f, std::vector<Formula> *clauses) {
  AddIff(Formula{b}, f, clauses);
}  // namespace

// Cnfize b ⇔ (b₁ ∧ ... ∧ bₙ) using the following equalities and add
// to clauses:
//   b ⇔ (b₁ ∧ ... ∧ bₙ)
// = (b → (b₁ ∧ ... ∧ bₙ)) ∧ ((b₁ ∧ ... ∧ bₙ) → b)
// = (¬b ∨ (b₁ ∧ ... ∧ bₙ)) ∧ (¬b₁ ∨ ... ∨ ¬bₙ ∨ b)
// = (¬b ∨ b₁) ∧ ... (¬b ∨ bₙ) ∧ (¬b₁ ∨ ... ∨ ¬bₙ ∨ b)   (✓CNF)
void CnfizeConjunction(const Variable &b, const Formula &f, std::vector<Formula> *clauses) {
  // operands = {b₁, ..., bₙ}
  const std::set<Formula> &operands{get_operands(f)};
  // negated_operands = {¬b₁, ..., ¬bₙ}
  const std::set<Formula> &negated_operands{map(operands, [](const Formula &formula) { return !formula; })};
  Formula ret{Formula::True()};
  for (const Formula &b_i : operands) {
    Add(!b || b_i, clauses);
  }
  Add(make_disjunction(negated_operands) || b, clauses);
}

// Cnfize b ⇔ (b₁ ∨ ... ∨ bₙ) using the following equalities and add
// to clauses:
//   b ⇔ (b₁ ∨ ... ∨ bₙ)
// = (b → (b₁ ∨ ... ∨ bₙ)) ∧ ((b₁ ∨ ... ∨ bₙ) → b)
// = (¬b ∨ b₁ ∨ ... ∨ bₙ) ∧ ((¬b₁ ∧ ... ∧ ¬bₙ) ∨ b)
// = (¬b ∨ b₁ ∨ ... ∨ bₙ) ∧ (¬b₁ ∨ b) ∧ ... ∧ (¬bₙ ∨ b)   (✓CNF)
void CnfizeDisjunction(const Variable &b, const Formula &f, std::vector<Formula> *clauses) {
  // negated_operands = {¬b₁, ..., ¬bₙ}
  const std::set<Formula> &negated_operands{map(get_operands(f), [](const Formula &formula) { return !formula; })};
  Add(!b || f, clauses);  // (¬b ∨ b₁ ∨ ... ∨ bₙ)
  for (const Formula &neg_b_i : negated_operands) {
    Add(neg_b_i || b, clauses);
  }
}

}  // namespace

}  // namespace dlinear
