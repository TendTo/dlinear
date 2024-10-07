/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */

#include "NaiveCnfizer.h"

#include <numeric>
#include <set>

#include "dlinear/util/exception.h"

namespace dlinear {

// The main function of the NaiveCnfizer:
//  - It visits each node and introduce a Boolean variable `b` for
//    each subterm `f`, and keep the relation `b ⇔ f`.
//  - Then it cnfizes each `b ⇔ f` and make a conjunction of them.
Formula NaiveCnfizer::Convert(const Formula &f) {
  // TODO(soonho): Using cache if needed.
  return Visit(nnfizer_.Convert(f, true));
}

Formula NaiveCnfizer::VisitEqualTo(const Formula &f) {
  const Expression &lhs{get_lhs_expression(f)};
  const Expression &rhs{get_rhs_expression(f)};
  return (lhs >= rhs) && (lhs <= rhs);
}
Formula NaiveCnfizer::VisitNotEqualTo(const Formula &f) {
  const Expression &lhs{get_lhs_expression(f)};
  const Expression &rhs{get_rhs_expression(f)};
  return (lhs > rhs) || (lhs < rhs);
}
Formula NaiveCnfizer::VisitForall(const Formula &f) {
  // f = ∀y. φ(x, y).
  const Variables &quantified_variables{get_quantified_variables(f)};  // y
  const Formula &quantified_formula{get_quantified_formula(f)};        // φ(x, y)
  return forall(quantified_variables, Convert(quantified_formula));
}

Formula NaiveCnfizer::VisitConjunction(const Formula &f) {
  const std::set<Formula> transformed_operands{
      map(get_operands(f), [this](const Formula &formula) { return this->Visit(formula); })};
  return make_conjunction(transformed_operands);
}

Formula NaiveCnfizer::VisitDisjunction(const Formula &f) {
  const std::set<Formula> &transformed_operands{
      map(get_operands(f), [this](const Formula &formula) { return this->Visit(formula); })};
  return std::accumulate(transformed_operands.begin(), transformed_operands.end(), Formula::False(),
                         [](const Formula &cnf1, const Formula &cnf2) {
                           std::set<Formula> clauses;
                           if (is_conjunction(cnf1)) {
                             if (is_conjunction(cnf2)) {
                               // Both of cnf1 and cnf2 are conjunctions.
                               for (const Formula &c1 : get_operands(cnf1)) {
                                 for (const Formula &c2 : get_operands(cnf2)) {
                                   clauses.insert(c1 || c2);
                                 }
                               }
                             } else {
                               // Only cnf1 is a conjunction.
                               for (const Formula &c1 : get_operands(cnf1)) {
                                 clauses.insert(c1 || cnf2);
                               }
                             }
                           } else {
                             if (is_conjunction(cnf2)) {
                               // Only cnf2 is a conjunction.
                               for (const Formula &c2 : get_operands(cnf2)) {
                                 clauses.insert(cnf1 || c2);
                               }
                             } else {
                               // None of them is a conjunction.
                               clauses.insert(cnf1 || cnf2);
                             }
                           }
                           return make_conjunction(clauses);
                         });
}

Formula NaiveCnfizer::VisitNegation(const Formula &f) {
  DLINEAR_ASSERT(is_atomic(get_operand(f)), "The formula must be atomic");
  return f;
}

}  // namespace dlinear
