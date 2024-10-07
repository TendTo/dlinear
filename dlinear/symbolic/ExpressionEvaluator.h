/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Expression evaluator class.
 */
#pragma once

#include <iosfwd>

#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Interval.h"

namespace dlinear {

/**
 * Evaluate an expression with a given box.
 *
 * The ExpressionEvaluator is used to evaluate an expression with a given box.
 * The box provides the values of the variables in the expression with intervals.
 */
class ExpressionEvaluator {
 public:
  explicit ExpressionEvaluator(Expression e);

  /// Evaluates the expression with @p box.
  Interval operator()(const Box& box) const;

  [[nodiscard]] const Variables& variables() const { return e_.GetVariables(); }

  [[nodiscard]] const Expression& expression() const { return e_; }

 private:
  [[nodiscard]] Interval Visit(const Expression& e, const Box& box) const;
  static Interval VisitVariable(const Expression& e, const Box& box);
  static Interval VisitConstant(const Expression& e, const Box& box);
  static Interval VisitRealConstant(const Expression& e, const Box& box);
  [[nodiscard]] Interval VisitAddition(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitMultiplication(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitDivision(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitLog(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitAbs(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitExp(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitSqrt(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitPow(const Expression& e, const Box& box) const;

  // Evaluates `pow(e1, e2)` with the @p box.
  [[nodiscard]] Interval VisitPow(const Expression& e1, const Expression& e2, const Box& box) const;
  [[nodiscard]] Interval VisitSin(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitCos(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitTan(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitAsin(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitAcos(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitAtan(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitAtan2(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitSinh(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitCosh(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitTanh(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitMin(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitMax(const Expression& e, const Box& box) const;
  static Interval VisitIfThenElse(const Expression& e, const Box& box);
  static Interval VisitUninterpretedFunction(const Expression& e, const Box& box);

  // Makes VisitExpression a friend of this class so that it can use private
  // operator()s.
  friend Interval drake::symbolic::VisitExpression<Interval>(const ExpressionEvaluator*, const Expression&, const Box&);

  const Expression e_;
};

std::ostream& operator<<(std::ostream& os, const ExpressionEvaluator& expression_evaluator);

}  // namespace dlinear
