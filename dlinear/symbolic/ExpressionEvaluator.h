/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Expression evaluator class.
 */
#pragma once

#include <iosfwd>

#include "dlinear/symbolic/GenericExpressionVisitor.h"
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
class ExpressionEvaluator : public GenericExpressionVisitor<Interval, const Box&> {
 public:
  /**
   * Construct a new ExpressionEvaluator object with the given expression and configuration.
   * @param e expression to evaluate
   * @param config configuration to use
   */
  ExpressionEvaluator(Expression e, const Config& config);

  /// Evaluates the expression with @p box.
  [[nodiscard]] Interval Process(const Box& box) const;
  [[nodiscard]] Interval operator()(const Box& box) const;

  [[nodiscard]] const Variables& variables() const { return e_.GetVariables(); }
  [[nodiscard]] const Expression& expression() const { return e_; }

 private:
  [[nodiscard]] Interval VisitVariable(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitConstant(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitRealConstant(const Expression& e, const Box& box) const;
  [[nodiscard]] Interval VisitAddition(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitMultiplication(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitDivision(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitLog(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitAbs(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitExp(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitSqrt(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitPow(const Expression& e, const Box& box) const override;

  // Evaluates `pow(e1, e2)` with the @p box.
  [[nodiscard]] Interval VisitPow(const Expression& e1, const Expression& e2, const Box& box) const;
  [[nodiscard]] Interval VisitSin(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitCos(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitTan(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitAsin(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitAcos(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitAtan(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitAtan2(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitSinh(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitCosh(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitTanh(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitMin(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitMax(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitIfThenElse(const Expression& e, const Box& box) const override;
  [[nodiscard]] Interval VisitUninterpretedFunction(const Expression& e, const Box& box) const override;

  const Expression e_;
};

std::ostream& operator<<(std::ostream& os, const ExpressionEvaluator& expression_evaluator);

}  // namespace dlinear
