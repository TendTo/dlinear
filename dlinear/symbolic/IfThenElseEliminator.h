/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @copyrignt 2017 Toyota Research Institute (dreal4)
 * @licence BSD 3-Clause License
 * IfThenElseEliminator class.
 */
#pragma once

#include <unordered_set>
#include <vector>

#include "dlinear/symbolic/FormulaVisitor.h"
#include "dlinear/symbolic/GenericExpressionVisitor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Stats.h"

namespace dlinear {
/**
 * IfThenElseEliminator class
 *
 * Eliminate If-Then-Else expressions by introducing new variables.
 * @todo Check "Efficient Term ITE Conversion for Satisfiability Modulo Theories", H. Kim, F. Somenzi, H. Jin. Twelfth
 * International Conference on Theory and Applications of Satisfiability Testing (SAT'09).
 */
class IfThenElseEliminator : public FormulaVisitor<const Formula &>,
                             public GenericExpressionVisitor<Expression, const Formula &> {
 public:
  using FormulaVisitor::stats;

  explicit IfThenElseEliminator(const Config &config)
      : FormulaVisitor<const Formula &>{config, "IfThenElseEliminator"},
        GenericExpressionVisitor<Expression, const Formula &>{config, "IfThenElseEliminator"},
        counter_{0} {}
  /**
   * Returns a equisatisfiable formula by eliminating if-then-expressions in @p f by introducing new variables.
   * @param f Formula to be processed.
   * @return Processed formula.
   */
  [[nodiscard]] Formula Process(const Formula &f);
  [[nodiscard]] std::pair<Expression, Formula> Process(const Expression &e);
  [[nodiscard]] const std::unordered_map<Expression, Variable> &variables() const;

 private:
  // Handle expressions.
  Expression VisitExpression(const Expression &e, const Formula &guard) const override;
  Expression VisitVariable(const Expression &e, const Formula &guard) const override;
  Expression VisitConstant(const Expression &e, const Formula &guard) const override;
  Expression VisitAddition(const Expression &e, const Formula &guard) const override;
  Expression VisitMultiplication(const Expression &e, const Formula &guard) const override;
  Expression VisitDivision(const Expression &e, const Formula &guard) const override;
  Expression VisitLog(const Expression &e, const Formula &guard) const override;
  Expression VisitAbs(const Expression &e, const Formula &guard) const override;
  Expression VisitExp(const Expression &e, const Formula &guard) const override;
  Expression VisitSqrt(const Expression &e, const Formula &guard) const override;
  Expression VisitPow(const Expression &e, const Formula &guard) const override;
  Expression VisitSin(const Expression &e, const Formula &guard) const override;
  Expression VisitCos(const Expression &e, const Formula &guard) const override;
  Expression VisitTan(const Expression &e, const Formula &guard) const override;
  Expression VisitAsin(const Expression &e, const Formula &guard) const override;
  Expression VisitAcos(const Expression &e, const Formula &guard) const override;
  Expression VisitAtan(const Expression &e, const Formula &guard) const override;
  Expression VisitAtan2(const Expression &e, const Formula &guard) const override;
  Expression VisitSinh(const Expression &e, const Formula &guard) const override;
  Expression VisitCosh(const Expression &e, const Formula &guard) const override;
  Expression VisitTanh(const Expression &e, const Formula &guard) const override;
  Expression VisitMin(const Expression &e, const Formula &guard) const override;
  Expression VisitMax(const Expression &e, const Formula &guard) const override;
  Expression VisitIfThenElse(const Expression &e, const Formula &guard) const override;
  Expression VisitUninterpretedFunction(const Expression &e, const Formula &guard) const override;

  // Handle formula
  Formula VisitFalse(const Formula &f, const Formula &guard) const override;
  Formula VisitTrue(const Formula &f, const Formula &guard) const override;
  Formula VisitVariable(const Formula &f, const Formula &guard) const override;
  Formula VisitEqualTo(const Formula &f, const Formula &guard) const override;
  Formula VisitNotEqualTo(const Formula &f, const Formula &guard) const override;
  Formula VisitGreaterThan(const Formula &f, const Formula &guard) const override;
  Formula VisitGreaterThanOrEqualTo(const Formula &f, const Formula &guard) const override;
  Formula VisitLessThan(const Formula &f, const Formula &guard) const override;
  Formula VisitLessThanOrEqualTo(const Formula &f, const Formula &guard) const override;
  Formula VisitConjunction(const Formula &f, const Formula &guard) const override;
  Formula VisitDisjunction(const Formula &f, const Formula &guard) const override;
  Formula VisitNegation(const Formula &f, const Formula &guard) const override;
  Formula VisitForall(const Formula &f, const Formula &guard) const override;

  // ---------------
  // Member fields
  // ---------------

  mutable std::vector<Formula> added_formulas_;  ///< The added formulas introduced by the elimination process. Resets
                                                 ///< after each call to Process.
  mutable std::unordered_set<Variable> ite_variables_;  ///< The variables introduced by the elimination process.
  mutable std::unordered_map<Expression, Variable>
      ite_to_var_;  ///< Mapping from ITE to the corresponding variable obtained by ITE elimination.
  mutable std::unordered_map<Variable, Formula>
      ite_var_to_formulas_;  ///< Mapping from ITE to the corresponding variable obtained by ITE elimination.

  mutable std::size_t counter_;  ///< Counter for the number of introduced variables.
};

}  // namespace dlinear
