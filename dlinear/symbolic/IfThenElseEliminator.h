/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * IfThenElseEliminator class.
 */
#pragma once

#include <unordered_set>
#include <vector>

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
class IfThenElseEliminator {
 public:
  explicit IfThenElseEliminator(const Config &config)
      : counter_{0}, config_{config}, stats_{config.with_timings(), "IfThenElseEliminator", "Process"} {}
  /**
   * Returns a equisatisfiable formula by eliminating if-then-expressions in @p f by introducing new variables.
   * @param f Formula to be processed.
   * @return Processed formula.
   */
  Formula Process(const Formula &f);
  std::pair<Expression, Formula> Process(const Expression &e);
  const std::unordered_map<Expression, Variable> &variables() const;
  const IterationStats &stats() const { return stats_; }

 private:
  // Handle expressions.
  Expression Visit(const Expression &e, const Formula &guard);
  Expression VisitVariable(const Expression &e, const Formula &guard);
  Expression VisitConstant(const Expression &e, const Formula &guard);
  Expression VisitAddition(const Expression &e, const Formula &guard);
  Expression VisitMultiplication(const Expression &e, const Formula &guard);
  Expression VisitDivision(const Expression &e, const Formula &guard);
  Expression VisitLog(const Expression &e, const Formula &guard);
  Expression VisitAbs(const Expression &e, const Formula &guard);
  Expression VisitExp(const Expression &e, const Formula &guard);
  Expression VisitSqrt(const Expression &e, const Formula &guard);
  Expression VisitPow(const Expression &e, const Formula &guard);
  Expression VisitSin(const Expression &e, const Formula &guard);
  Expression VisitCos(const Expression &e, const Formula &guard);
  Expression VisitTan(const Expression &e, const Formula &guard);
  Expression VisitAsin(const Expression &e, const Formula &guard);
  Expression VisitAcos(const Expression &e, const Formula &guard);
  Expression VisitAtan(const Expression &e, const Formula &guard);
  Expression VisitAtan2(const Expression &e, const Formula &guard);
  Expression VisitSinh(const Expression &e, const Formula &guard);
  Expression VisitCosh(const Expression &e, const Formula &guard);
  Expression VisitTanh(const Expression &e, const Formula &guard);
  Expression VisitMin(const Expression &e, const Formula &guard);
  Expression VisitMax(const Expression &e, const Formula &guard);
  Expression VisitIfThenElse(const Expression &e, const Formula &guard);
  Expression VisitUninterpretedFunction(const Expression &e, const Formula &guard);

  // Handle formula
  Formula Visit(const Formula &f, const Formula &guard);
  Formula VisitFalse(const Formula &f, const Formula &guard);
  Formula VisitTrue(const Formula &f, const Formula &guard);
  Formula VisitVariable(const Formula &f, const Formula &guard);
  Formula VisitEqualTo(const Formula &f, const Formula &guard);
  Formula VisitNotEqualTo(const Formula &f, const Formula &guard);
  Formula VisitGreaterThan(const Formula &f, const Formula &guard);
  Formula VisitGreaterThanOrEqualTo(const Formula &f, const Formula &guard);
  Formula VisitLessThan(const Formula &f, const Formula &guard);
  Formula VisitLessThanOrEqualTo(const Formula &f, const Formula &guard);
  Formula VisitConjunction(const Formula &f, const Formula &guard);
  Formula VisitDisjunction(const Formula &f, const Formula &guard);
  Formula VisitNegation(const Formula &f, const Formula &guard);
  Formula VisitForall(const Formula &f, const Formula &guard);

  // ---------------
  // Member fields
  // ---------------

  std::vector<Formula> added_formulas_;  ///< The added formulas introduced by the elimination process. Resets after
                                         ///< each call to Process.
  std::unordered_set<Variable> ite_variables_;  ///< The variables introduced by the elimination process.
  std::unordered_map<Expression, Variable>
      ite_to_var_;  ///< Mapping from ITE to the corresponding variable obtained by ITE elimination.
  std::unordered_map<Variable, Formula>
      ite_var_to_formulas_;  ///< Mapping from ITE to the corresponding variable obtained by ITE elimination.

  std::size_t counter_;   ///< Counter for the number of introduced variables.
  const Config& config_;  ///< Configuration of the elimination process.
  IterationStats stats_;  ///< Statistics of the elimination process.

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula>(IfThenElseEliminator *, const Formula &, const Formula &);
  // Makes VisitExpression a friend of this class so that it can use private
  // operator()s.
  friend Expression drake::symbolic::VisitExpression<Expression>(IfThenElseEliminator *, const Expression &,
                                                                 const Formula &);
};

}  // namespace dlinear
