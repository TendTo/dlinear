/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */

#include "IfThenElseEliminator.h"

#include <map>
#include <set>
#include <string>
#include <utility>

#include "dlinear/libs/libgmp.h"
#include "dlinear/symbolic/Nnfizer.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"

namespace dlinear {

Formula IfThenElseEliminator::Process(const Formula &f) {
  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();

  added_formulas_.clear();

  Formula new_f{Visit(f, Formula::True())};
  if (f.EqualTo(new_f) && added_formulas_.empty()) return f;
  return new_f && make_conjunction(added_formulas_);
}
std::pair<Expression, Formula> IfThenElseEliminator::Process(const Expression &e) {
  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();

  added_formulas_.clear();

  Expression new_e{Visit(e, Formula::True())};
  if (e.EqualTo(new_e) && added_formulas_.empty()) return {e, {}};
  return {new_e, make_conjunction(added_formulas_)};
}

const std::unordered_map<Expression, Variable> &IfThenElseEliminator::variables() const {
  return ite_to_var_;
}

Expression IfThenElseEliminator::Visit(const Expression &e, const Formula &guard) {
  if (e.include_ite()) return VisitExpression<Expression>(this, e, guard);
  return e;
}

Expression IfThenElseEliminator::VisitVariable(const Expression &e, const Formula &) { return e; }

Expression IfThenElseEliminator::VisitConstant(const Expression &e, const Formula &) { return e; }

Expression IfThenElseEliminator::VisitAddition(const Expression &e, const Formula &guard) {
  // e = c₀ + ∑ᵢ cᵢ * eᵢ
  Expression ret{get_constant_in_addition(e)};
  for (const auto &p : get_expr_to_coeff_map_in_addition(e)) {
    const Expression &e_i{p.first};
    const mpq_class &c_i{p.second};
    ret += c_i * Visit(e_i, guard);
  }
  return ret;
}

Expression IfThenElseEliminator::VisitMultiplication(const Expression &e, const Formula &guard) {
  // e = c₀ * ∏ᵢ pow(eᵢ₁, eᵢ₂)
  Expression ret{get_constant_in_multiplication(e)};
  for (const auto &p : get_base_to_exponent_map_in_multiplication(e)) {
    const Expression &e_i1{p.first};
    const Expression &e_i2{p.second};
    ret *= pow(Visit(e_i1, guard), Visit(e_i2, guard));
  }
  return ret;
}

Expression IfThenElseEliminator::VisitDivision(const Expression &e, const Formula &guard) {
  return Visit(get_first_argument(e), guard) / Visit(get_second_argument(e), guard);
}

Expression IfThenElseEliminator::VisitLog(const Expression &e, const Formula &guard) {
  return log(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitAbs(const Expression &e, const Formula &guard) {
  return abs(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitExp(const Expression &e, const Formula &guard) {
  return exp(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitSqrt(const Expression &e, const Formula &guard) {
  return sqrt(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitPow(const Expression &e, const Formula &guard) {
  return pow(Visit(get_first_argument(e), guard), Visit(get_second_argument(e), guard));
}

Expression IfThenElseEliminator::VisitSin(const Expression &e, const Formula &guard) {
  return sin(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitCos(const Expression &e, const Formula &guard) {
  return cos(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitTan(const Expression &e, const Formula &guard) {
  return tan(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitAsin(const Expression &e, const Formula &guard) {
  return asin(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitAcos(const Expression &e, const Formula &guard) {
  return acos(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitAtan(const Expression &e, const Formula &guard) {
  return atan(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitAtan2(const Expression &e, const Formula &guard) {
  return atan2(Visit(get_first_argument(e), guard), Visit(get_second_argument(e), guard));
}

Expression IfThenElseEliminator::VisitSinh(const Expression &e, const Formula &guard) {
  return sinh(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitCosh(const Expression &e, const Formula &guard) {
  return cosh(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitTanh(const Expression &e, const Formula &guard) {
  return tanh(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitMin(const Expression &e, const Formula &guard) {
  return min(Visit(get_first_argument(e), guard), Visit(get_second_argument(e), guard));
}

Expression IfThenElseEliminator::VisitMax(const Expression &e, const Formula &guard) {
  return max(Visit(get_first_argument(e), guard), Visit(get_second_argument(e), guard));
}

Expression IfThenElseEliminator::VisitIfThenElse(const Expression &e, const Formula &guard) {
  // Both then and else expressions are the same.
  const auto it = ite_to_var_.find(e);
  if (it != ite_to_var_.end()) {
    added_formulas_.push_back(ite_var_to_formulas_.at(it->second));
    return it->second;
  }
  if (get_then_expression(e).EqualTo(get_else_expression(e))) return Visit(get_then_expression(e), guard);

  const Formula c{Visit(get_conditional_formula(e), guard)};

  // If the guard is the same (or inverted) as the current condition, short-circuit the ITE.
  if (c.EqualTo(guard)) return Visit(get_then_expression(e), guard);
  if (c.EqualTo(!guard)) return Visit(get_else_expression(e), guard);

  const Variable new_var{"ITE" + std::to_string(counter_++), Variable::Type::CONTINUOUS};
  const Formula then_guard{guard && c};
  const Formula else_guard{guard && !c};
  const Expression e1{Visit(get_then_expression(e), then_guard)};
  const Expression e2{Visit(get_else_expression(e), else_guard)};
  added_formulas_.push_back(!then_guard || (new_var == e1));  // then_guard => (new_var = e1)
  added_formulas_.push_back(!else_guard || (new_var == e2));  // else_guard => (new_var = e2)
  ite_to_var_.emplace(e, new_var);
  ite_var_to_formulas_.emplace(new_var, added_formulas_.back() && *(added_formulas_.rbegin() + 1));
  return new_var;
}

Expression IfThenElseEliminator::VisitUninterpretedFunction(const Expression &e, const Formula &) { return e; }

Formula IfThenElseEliminator::Visit(const Formula &f, const Formula &guard) {
  return VisitFormula<Formula>(this, f, guard);
}

Formula IfThenElseEliminator::VisitFalse(const Formula &f, const Formula &) { return f; }

Formula IfThenElseEliminator::VisitTrue(const Formula &f, const Formula &) { return f; }

Formula IfThenElseEliminator::VisitVariable(const Formula &f, const Formula &) { return f; }

Formula IfThenElseEliminator::VisitEqualTo(const Formula &f, const Formula &guard) {
  return Visit(get_lhs_expression(f), guard) == Visit(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitNotEqualTo(const Formula &f, const Formula &guard) {
  return Visit(get_lhs_expression(f), guard) != Visit(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitGreaterThan(const Formula &f, const Formula &guard) {
  return Visit(get_lhs_expression(f), guard) > Visit(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitGreaterThanOrEqualTo(const Formula &f, const Formula &guard) {
  return Visit(get_lhs_expression(f), guard) >= Visit(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitLessThan(const Formula &f, const Formula &guard) {
  return Visit(get_lhs_expression(f), guard) < Visit(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitLessThanOrEqualTo(const Formula &f, const Formula &guard) {
  return Visit(get_lhs_expression(f), guard) <= Visit(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitConjunction(const Formula &f, const Formula &guard) {
  // f := f₁ ∧ ... ∧ fₙ
  std::set<Formula> new_conjuncts;
  for (const Formula &f_i : get_operands(f)) {
    new_conjuncts.emplace(Visit(f_i, guard));
  }
  return make_conjunction(new_conjuncts);
}

Formula IfThenElseEliminator::VisitDisjunction(const Formula &f, const Formula &guard) {
  // f := f₁ ∨ ... ∨ fₙ
  std::set<Formula> new_disjuncts;
  for (const Formula &f_i : get_operands(f)) {
    new_disjuncts.emplace(Visit(f_i, guard));
  }
  return make_disjunction(new_disjuncts);
}

Formula IfThenElseEliminator::VisitNegation(const Formula &f, const Formula &guard) {
  return !Visit(get_operand(f), guard);
}

Formula IfThenElseEliminator::VisitForall(const Formula &f, const Formula &) {
  //    ∃x. ∀y. ITE(f, e₁, e₂) > 0
  // => ∃x. ¬∃y. ¬(ITE(f, e₁, e₂) > 0)
  // => ∃x. ¬∃y. ∃v. ¬(v > 0) ∧ (f → (v = e₁)) ∧ (¬f → (v = e₂))
  // => ∃x. ∀y. ∀v. ¬(¬(v > 0) ∧ (f → (v = e₁)) ∧ (¬f → (v = e₂)))
  // => ∃x. ∀y. ∀v. (v > 0) ∨ ¬((f → (v = e₁)) ∧ (¬f → (v = e₂)))
  // => ∃x. ∀y. ∀v. ¬((f → (v = e₁)) ∧ (¬f → (v = e₂))) ∨ (v > 0)
  // => ∃x. ∀y. ∀v. ((f → (v = e₁)) ∧ (¬f → (v = e₂))) → (v > 0)
  // => ∃x. ∀y. ∀v. (v > 0) ∨ (f ∧ (v ≠ e₁)) ∨ (¬f ∧ (v ≠ e₂)).

  // Note that we have the following:
  // => ∃x. ∀y. ∀v. ¬(¬(v > 0)) ∧ ¬(f ∧ (v ≠ e₁)) ∧ ¬(¬f ∧ (v ≠ e₂)).
  // => ∃x. ∀y. ∀v. ¬(¬(v > 0)) ∧ (¬f ∨ (v = e₁)) ∧ (f ∨ (v = e₂)).
  // => ∃x. ∀y. ∀v. ¬(¬(v > 0)) ∧ (f → (v = e₁)) ∧ (¬f → (v = e₂)).
  //
  // That is, we can first process the negation of the original
  // formula `ITE(f, e₁, e₂) > 0`, then negate the result again while
  // collecting the newly introduced variables (`v`s) to treat them as
  // universally quantified variables (instead of existential
  // variables). In this way, we can use the existing ITE-elim routine.
  Variables quantified_variables{get_quantified_variables(f)};
  const Formula &quantified_formula{get_quantified_formula(f)};
  IfThenElseEliminator ite_eliminator_forall{config_};
  const Formula eliminated{ite_eliminator_forall.Process(!quantified_formula)};
  for (const auto &[_, v] : ite_eliminator_forall.variables()) {
    quantified_variables.insert(v);
  }
  return forall(quantified_variables, Nnfizer{config_}.Convert(!eliminated));
}

}  // namespace dlinear
