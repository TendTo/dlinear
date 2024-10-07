/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "ExpressionEvaluator.h"

#include <map>
#include <numeric>
#include <ostream>
#include <utility>

#include "dlinear/libs/libgmp.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/exception.h"

namespace dlinear {

ExpressionEvaluator::ExpressionEvaluator(Expression e) : e_{std::move(e)} {}

Interval ExpressionEvaluator::operator()(const Box& box) const { return Visit(e_, box); }

Interval ExpressionEvaluator::Visit(const Expression& e, const Box& box) const {
  return VisitExpression<Interval>(this, e, box);
}

Interval ExpressionEvaluator::VisitVariable(const Expression& e, const Box& box) {
  const Variable& var{get_variable(e)};
  return box[var];
}

Interval ExpressionEvaluator::VisitConstant(const Expression& e, const Box&) { return Interval{get_constant_value(e)}; }

Interval ExpressionEvaluator::VisitRealConstant(const Expression&, const Box&) {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitAddition(const Expression& e, const Box& box) const {
  const mpq_class& c{get_constant_in_addition(e)};
  const auto& expr_to_coeff_map = get_expr_to_coeff_map_in_addition(e);
  return std::accumulate(expr_to_coeff_map.begin(), expr_to_coeff_map.end(), Interval{c},
                         [this, &box](const Interval& init, const std::pair<const Expression, mpq_class>& p) {
                           return init + Visit(p.first, box) * p.second;
                         });
}

Interval ExpressionEvaluator::VisitMultiplication(const Expression& e, const Box& box) const {
  const mpq_class& c{get_constant_in_multiplication(e)};
  const auto& base_to_exponent_map = get_base_to_exponent_map_in_multiplication(e);
  return accumulate(base_to_exponent_map.begin(), base_to_exponent_map.end(), Interval{c},
                    [this, &box](const Interval& init, const std::pair<const Expression, Expression>& p) {
                      return init * VisitPow(p.first, p.second, box);
                    });
}

Interval ExpressionEvaluator::VisitDivision(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitLog(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitAbs(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitExp(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitSqrt(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitPow(const Expression& e, const Box& box) const {
  return VisitPow(get_first_argument(e), get_second_argument(e), box);
}

Interval ExpressionEvaluator::VisitPow(const Expression&, const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
#if 0
  const Interval first{Visit(e1, box)};
  const Interval second{Visit(e2, box)};
  if (second.is_degenerated() && !second.is_empty()) {
    DLINEAR_ASSERT(second.lb() == second.ub(), "Interval must be a point.");
    const double point{second.lb()};
    if (is_integer(point)) {
      if (point == 2.0) {
        return sqr(first);
      } else {
        return pow(first, static_cast<int>(point));
      }
    } else {
      return pow(first, point);
    }
  } else {
    return pow(first, second);
  }
#endif
}

Interval ExpressionEvaluator::VisitSin(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitCos(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitTan(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitAsin(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitAcos(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitAtan(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitAtan2(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitSinh(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitCosh(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitTanh(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitMin(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitMax(const Expression&, const Box&) const {
  DLINEAR_RUNTIME_ERROR("Operation is not supported yet.");
}

Interval ExpressionEvaluator::VisitIfThenElse(const Expression& /* unused */, const Box& /* unused */) {
  DLINEAR_RUNTIME_ERROR("If-then-else expression is not supported yet.");
}

Interval ExpressionEvaluator::VisitUninterpretedFunction(const Expression& /* unused */, const Box& /* unused */) {
  DLINEAR_RUNTIME_ERROR("Uninterpreted function is not supported.");
}

std::ostream& operator<<(std::ostream& os, const ExpressionEvaluator& expression_evaluator) {
  return os << "ExpressionEvaluator(" << expression_evaluator.expression() << ")";
}

}  // namespace dlinear
