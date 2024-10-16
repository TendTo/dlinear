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
  const TimerGuard timer_guard(&FormulaVisitor::stats_.m_timer(), FormulaVisitor::stats_.enabled());
  FormulaVisitor::stats_.Increase();

  added_formulas_.clear();

  const Formula new_f{VisitFormula(f, Formula::True())};
  if (f.EqualTo(new_f) && added_formulas_.empty()) return f;
  return new_f && make_conjunction(added_formulas_);
}
std::pair<Expression, Formula> IfThenElseEliminator::Process(const Expression &e) {
  const TimerGuard timer_guard(&FormulaVisitor::stats_.m_timer(), FormulaVisitor::stats_.enabled());
  FormulaVisitor::stats_.Increase();

  added_formulas_.clear();

  const Expression new_e{VisitExpression(e, Formula::True())};
  if (e.EqualTo(new_e) && added_formulas_.empty()) return {e, {}};
  return {new_e, make_conjunction(added_formulas_)};
}

const std::unordered_map<Expression, Variable> &IfThenElseEliminator::variables() const { return ite_to_var_; }

Expression IfThenElseEliminator::VisitExpression(const Expression &e, const Formula &guard) const {
  return e.include_ite() ? GenericExpressionVisitor::VisitExpression(e, guard) : e;
}

Expression IfThenElseEliminator::VisitVariable(const Expression &e, const Formula &) const { return e; }

Expression IfThenElseEliminator::VisitConstant(const Expression &e, const Formula &) const { return e; }

Expression IfThenElseEliminator::VisitAddition(const Expression &e, const Formula &guard) const {
  // e = c₀ + ∑ᵢ cᵢ * eᵢ
  Expression ret{get_constant_in_addition(e)};
  for (const auto &p : get_expr_to_coeff_map_in_addition(e)) {
    const Expression &e_i{p.first};
    const mpq_class &c_i{p.second};
    ret += c_i * VisitExpression(e_i, guard);
  }
  return ret;
}

Expression IfThenElseEliminator::VisitMultiplication(const Expression &e, const Formula &guard) const {
  // e = c₀ * ∏ᵢ pow(eᵢ₁, eᵢ₂)
  Expression ret{get_constant_in_multiplication(e)};
  for (const auto &p : get_base_to_exponent_map_in_multiplication(e)) {
    const Expression &e_i1{p.first};
    const Expression &e_i2{p.second};
    ret *= pow(VisitExpression(e_i1, guard), VisitExpression(e_i2, guard));
  }
  return ret;
}

Expression IfThenElseEliminator::VisitDivision(const Expression &e, const Formula &guard) const {
  return VisitExpression(get_first_argument(e), guard) / VisitExpression(get_second_argument(e), guard);
}

Expression IfThenElseEliminator::VisitLog(const Expression &e, const Formula &guard) const {
  return log(VisitExpression(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitAbs(const Expression &e, const Formula &guard) const {
  return abs(VisitExpression(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitExp(const Expression &e, const Formula &guard) const {
  return exp(VisitExpression(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitSqrt(const Expression &e, const Formula &guard) const {
  return sqrt(VisitExpression(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitPow(const Expression &e, const Formula &guard) const {
  return pow(VisitExpression(get_first_argument(e), guard), VisitExpression(get_second_argument(e), guard));
}

Expression IfThenElseEliminator::VisitSin(const Expression &e, const Formula &guard) const {
  return sin(VisitExpression(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitCos(const Expression &e, const Formula &guard) const {
  return cos(VisitExpression(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitTan(const Expression &e, const Formula &guard) const {
  return tan(VisitExpression(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitAsin(const Expression &e, const Formula &guard) const {
  return asin(VisitExpression(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitAcos(const Expression &e, const Formula &guard) const {
  return acos(VisitExpression(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitAtan(const Expression &e, const Formula &guard) const {
  return atan(VisitExpression(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitAtan2(const Expression &e, const Formula &guard) const {
  return atan2(VisitExpression(get_first_argument(e), guard), VisitExpression(get_second_argument(e), guard));
}

Expression IfThenElseEliminator::VisitSinh(const Expression &e, const Formula &guard) const {
  return sinh(VisitExpression(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitCosh(const Expression &e, const Formula &guard) const {
  return cosh(VisitExpression(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitTanh(const Expression &e, const Formula &guard) const {
  return tanh(VisitExpression(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitMin(const Expression &e, const Formula &guard) const {
  return min(VisitExpression(get_first_argument(e), guard), VisitExpression(get_second_argument(e), guard));
}

Expression IfThenElseEliminator::VisitMax(const Expression &e, const Formula &guard) const {
  return max(VisitExpression(get_first_argument(e), guard), VisitExpression(get_second_argument(e), guard));
}

Expression IfThenElseEliminator::VisitIfThenElse(const Expression &e, const Formula &guard) const {
  // Both then and else expressions are the same.
  const auto it = ite_to_var_.find(e);
  if (it != ite_to_var_.end()) {
    added_formulas_.push_back(ite_var_to_formulas_.at(it->second));
    return it->second;
  }
  if (get_then_expression(e).EqualTo(get_else_expression(e))) return VisitExpression(get_then_expression(e), guard);

  const Formula c{VisitFormula(get_conditional_formula(e), guard)};

  // If the guard is the same (or inverted) as the current condition, short-circuit the ITE.
  if (c.EqualTo(guard)) return VisitExpression(get_then_expression(e), guard);
  if (c.EqualTo(!guard)) return VisitExpression(get_else_expression(e), guard);

  const Variable new_var{"ITE" + std::to_string(counter_++), Variable::Type::CONTINUOUS};
  const Formula then_guard{guard && c};
  const Formula else_guard{guard && !c};
  const Expression e1{VisitExpression(get_then_expression(e), then_guard)};
  const Expression e2{VisitExpression(get_else_expression(e), else_guard)};
  added_formulas_.push_back(!then_guard || (new_var == e1));  // then_guard => (new_var = e1)
  added_formulas_.push_back(!else_guard || (new_var == e2));  // else_guard => (new_var = e2)
  ite_to_var_.emplace(e, new_var);
  ite_var_to_formulas_.emplace(new_var, added_formulas_.back() && *(added_formulas_.rbegin() + 1));
  return new_var;
}

Expression IfThenElseEliminator::VisitUninterpretedFunction(const Expression &e, const Formula &) const { return e; }

Formula IfThenElseEliminator::VisitFalse(const Formula &f, const Formula &) const { return f; }

Formula IfThenElseEliminator::VisitTrue(const Formula &f, const Formula &) const { return f; }

Formula IfThenElseEliminator::VisitVariable(const Formula &f, const Formula &) const { return f; }

Formula IfThenElseEliminator::VisitEqualTo(const Formula &f, const Formula &guard) const {
  return VisitExpression(get_lhs_expression(f), guard) == VisitExpression(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitNotEqualTo(const Formula &f, const Formula &guard) const {
  return VisitExpression(get_lhs_expression(f), guard) != VisitExpression(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitGreaterThan(const Formula &f, const Formula &guard) const {
  return VisitExpression(get_lhs_expression(f), guard) > VisitExpression(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitGreaterThanOrEqualTo(const Formula &f, const Formula &guard) const {
  return VisitExpression(get_lhs_expression(f), guard) >= VisitExpression(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitLessThan(const Formula &f, const Formula &guard) const {
  return VisitExpression(get_lhs_expression(f), guard) < VisitExpression(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitLessThanOrEqualTo(const Formula &f, const Formula &guard) const {
  return VisitExpression(get_lhs_expression(f), guard) <= VisitExpression(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitConjunction(const Formula &f, const Formula &guard) const {
  // f := f₁ ∧ ... ∧ fₙ
  std::set<Formula> new_conjuncts;
  for (const Formula &f_i : get_operands(f)) {
    new_conjuncts.emplace(VisitFormula(f_i, guard));
  }
  return make_conjunction(new_conjuncts);
}

Formula IfThenElseEliminator::VisitDisjunction(const Formula &f, const Formula &guard) const {
  // f := f₁ ∨ ... ∨ fₙ
  std::set<Formula> new_disjuncts;
  for (const Formula &f_i : get_operands(f)) {
    new_disjuncts.emplace(VisitFormula(f_i, guard));
  }
  return make_disjunction(new_disjuncts);
}

Formula IfThenElseEliminator::VisitNegation(const Formula &f, const Formula &guard) const {
  return !VisitFormula(get_operand(f), guard);
}

Formula IfThenElseEliminator::VisitForall(const Formula &f, const Formula &) const {
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
  IfThenElseEliminator ite_eliminator_forall{FormulaVisitor::config_};
  const Formula eliminated{ite_eliminator_forall.Process(!quantified_formula)};
  for (const auto &[_, v] : ite_eliminator_forall.variables()) {
    quantified_variables.insert(v);
  }
  return forall(quantified_variables, Nnfizer{FormulaVisitor::config_}.Process(!eliminated));
}

}  // namespace dlinear
