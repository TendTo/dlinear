/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */

#include "Nnfizer.h"

#include <set>

#include "dlinear/util/logging.h"

namespace dlinear {

Nnfizer::Nnfizer(const dlinear::Config &config) : FormulaVisitor<bool, bool>{config, "Nnfizer"} {}

Formula Nnfizer::Process(const Formula &f, bool push_negation_into_relationals) const {
  DLINEAR_TRACE_FMT("Nnfizer::Convert({}, {})", f, push_negation_into_relationals);
  const TimerGuard timer_guard{&stats_.m_timer(), stats_.enabled()};
  stats_.Increase();
  return VisitFormula(f, true, push_negation_into_relationals);
}
Formula Nnfizer::operator()(const Formula &f, const bool push_negation_into_relationals) const {
  return Process(f, push_negation_into_relationals);
}

Formula Nnfizer::VisitFalse(const Formula &, const bool polarity, const bool) const {
  // NNF(False)  = False
  // NNF(¬False) = True
  return polarity ? Formula::False() : Formula::True();
}

Formula Nnfizer::VisitTrue(const Formula &, const bool polarity, const bool) const {
  // NNF(True)  = True
  // NNF(¬True) = False
  return polarity ? Formula::True() : Formula::False();
}

Formula Nnfizer::VisitVariable(const Formula &f, const bool polarity, const bool) const {
  // NNF(b)  = b
  // NNF(¬b) = ¬b
  return polarity ? f : !f;
}

Formula Nnfizer::VisitEqualTo(const Formula &f, const bool polarity, const bool push_negation_into_relationals) const {
  if (polarity) return f;
  // push_negation_into_relationals ? ¬(e₁ = e₂) ↦ (e₁ ≠ e₂) : ¬f
  return push_negation_into_relationals ? get_lhs_expression(f) != get_rhs_expression(f) : !f;
}

Formula Nnfizer::VisitNotEqualTo(const Formula &f, const bool polarity,
                                 const bool push_negation_into_relationals) const {
  if (polarity) return f;
  // push_negation_into_relationals ? ¬(e₁ ≠ e₂) ↦ (e₁ = e₂) : ¬f
  return push_negation_into_relationals ? get_lhs_expression(f) == get_rhs_expression(f) : !f;
}

Formula Nnfizer::VisitGreaterThan(const Formula &f, const bool polarity,
                                  const bool push_negation_into_relationals) const {
  if (polarity) return f;
  // push_negation_into_relationals ? ¬(e₁ > e₂) ↦ (e₁ <= e₂) : ¬f
  return push_negation_into_relationals ? get_lhs_expression(f) <= get_rhs_expression(f) : !f;
}

Formula Nnfizer::VisitGreaterThanOrEqualTo(const Formula &f, const bool polarity,
                                           const bool push_negation_into_relationals) const {
  if (polarity) return f;
  // push_negation_into_relationals ? ¬(e₁ >= e₂) ↦ (e₁ < e₂) : ¬f
  return push_negation_into_relationals ? get_lhs_expression(f) < get_rhs_expression(f) : !f;
}

Formula Nnfizer::VisitLessThan(const Formula &f, const bool polarity, const bool push_negation_into_relationals) const {
  if (polarity) return f;
  // push_negation_into_relationals ? ¬(e₁ < e₂) ↦ (e₁ >= e₂) : ¬f
  return push_negation_into_relationals ? get_lhs_expression(f) >= get_rhs_expression(f) : !f;
}

Formula Nnfizer::VisitLessThanOrEqualTo(const Formula &f, const bool polarity,
                                        const bool push_negation_into_relationals) const {
  if (polarity) return f;
  // push_negation_into_relationals ? ¬(e₁ <= e₂) ↦ (e₁ > e₂) : ¬f
  return push_negation_into_relationals ? get_lhs_expression(f) > get_rhs_expression(f) : !f;
}

Formula Nnfizer::VisitConjunction(const Formula &f, const bool polarity,
                                  const bool push_negation_into_relationals) const {
  // NNF(f₁ ∧ ... ∨ fₙ)    = NNF(f₁) ∧ ... ∧ NNF(fₙ)
  // NNF(¬(f₁ ∧ ... ∨ fₙ)) = NNF(¬f₁) ∨ ... ∨ NNF(¬fₙ)
  const std::set<Formula> new_operands{
      map(get_operands(f), [this, polarity, push_negation_into_relationals](const Formula &formula) {
        return this->VisitFormula(formula, polarity, push_negation_into_relationals);
      })};
  return polarity ? make_conjunction(new_operands) : make_disjunction(new_operands);
}

Formula Nnfizer::VisitDisjunction(const Formula &f, const bool polarity,
                                  const bool push_negation_into_relationals) const {
  // NNF(f₁ ∨ ... ∨ fₙ)    = NNF(f₁) ∨ ... ∨ NNF(fₙ)
  // NNF(¬(f₁ ∨ ... ∨ fₙ)) = NNF(¬f₁) ∧ ... ∧ NNF(¬fₙ)
  const std::set<Formula> new_operands{
      map(get_operands(f), [this, polarity, push_negation_into_relationals](const Formula &formula) {
        return this->VisitFormula(formula, polarity, push_negation_into_relationals);
      })};
  return polarity ? make_disjunction(new_operands) : make_conjunction(new_operands);
}

Formula Nnfizer::VisitNegation(const Formula &f, const bool polarity, const bool push_negation_into_relationals) const {
  // NNF(¬f, ⊤) = NNF(f, ⊥)
  // NNF(¬f, ⊥) = NNF(f, ⊤)
  return VisitFormula(get_operand(f), !polarity, push_negation_into_relationals);
}

Formula Nnfizer::VisitForall(const Formula &f, const bool polarity, const bool) const {
  // NNF(∀v₁...vₙ. f)    =  ∀v₁...vₙ. f
  // NNF(¬(∀v₁...vₙ. f)) = ¬∀v₁...vₙ. f
  //
  // TODO(soonho-tri): The second case can be further reduced into
  // ∃v₁...vₙ. NNF(¬f). However, we do not have a representation
  // FormulaExists(∃) yet. Revisit this when we add FormulaExists.
  return polarity ? f : !f;
}

}  // namespace dlinear
