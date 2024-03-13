#pragma once

#include <cassert>
#include <stdexcept>
#include <utility>

#include "dlinear/symbolic/symbolic_expression.h"

namespace dlinear::drake::symbolic {

/**
 * Call visitor object @p v with a polynomial symbolic-expression @p e, and arguments @p args.
 * Visitor object is expected to implement the following methods which take @p f and @p args:
 * `VisitConstant`, `VisitVariable`, `VisitAddition`, `VisitMultiplication`, `VisitDivision`, `VisitPow`.
 * @pre e.is_polynomial() is true.
 * @tparam Result type of the result of the visit
 * @tparam Visitor type of visitor object which implements the visit methods
 * @tparam Args argument types
 * @param v pointer to the visitor object
 * @param e symbolic expression to visit
 * @param args arguments to pass to the visitor methods
 * @return result of the visit
 * @throw std::runtime_error if NaN is detected during a visit.
 */
template<typename Result, typename Visitor, typename... Args>
Result VisitPolynomial(Visitor *v, const Expression &e, Args &&... args) {
  assert(e.is_polynomial());
  switch (e.get_kind()) {
    case ExpressionKind::Constant:return v->VisitConstant(e, std::forward<Args>(args)...);

    case ExpressionKind::Var:return v->VisitVariable(e, std::forward<Args>(args)...);

    case ExpressionKind::Add:return v->VisitAddition(e, std::forward<Args>(args)...);

    case ExpressionKind::Mul:return v->VisitMultiplication(e, std::forward<Args>(args)...);

    case ExpressionKind::Div:return v->VisitDivision(e, std::forward<Args>(args)...);

    case ExpressionKind::Pow:return v->VisitPow(e, std::forward<Args>(args)...);

    case ExpressionKind::NaN:throw std::runtime_error("NaN is detected while visiting an expression.");

    case ExpressionKind::Infty:throw std::runtime_error("An infinity is detected while visiting an expression.");

    case ExpressionKind::Log:
    case ExpressionKind::Abs:
    case ExpressionKind::Exp:
    case ExpressionKind::Sqrt:
    case ExpressionKind::Sin:
    case ExpressionKind::Cos:
    case ExpressionKind::Tan:
    case ExpressionKind::Asin:
    case ExpressionKind::Acos:
    case ExpressionKind::Atan:
    case ExpressionKind::Atan2:
    case ExpressionKind::Sinh:
    case ExpressionKind::Cosh:
    case ExpressionKind::Tanh:
    case ExpressionKind::Min:
    case ExpressionKind::Max:
    case ExpressionKind::IfThenElse:
    case ExpressionKind::UninterpretedFunction:
      // Should not be reachable because of `DRAKE_ASSERT(e.is_polynomial())` at
      // the top.
      throw std::runtime_error("Should not be reachable.");
  }
  // Should not be reachable. But we need the following to avoid "control
  // reaches end of non-void function" gcc-warning.
  throw std::runtime_error("Should not be reachable.");
}

/**
 * Calls visitor object @p v with a symbolic-expression @p e, and arguments @p args.
 *
 * Visitor object is expected to implement the following methods which take @p f and @p args:
 * `VisitConstant`, `VisitVariable`, `VisitAddition`, `VisitMultiplication`, `VisitDivision`, `VisitLog`, `VisitAbs`,
 * `VisitExp`, `VisitSqrt`, `VisitPow`, `VisitSin`, `VisitCos`, `VisitTan`, `VisitAsin`, `VisitAtan`,
 * `VisitAtan2`, `VisitSinh`, `VisitCosh`, `VisitTanh`, `VisitMin`,
 * `VisitMax`, `VisitIfThenElse`, `VisitUninterpretedFunction.
 * @tparam Result type of the result of the visit
 * @tparam Visitor type of visitor object which implements the visit methods
 * @tparam Args argument types
 * @param v pointer to the visitor object
 * @param e symbolic expression to visit
 * @param args arguments to pass to the visitor methods
 * @return result of the visit
 * @throw std::runtime_error if NaN or an infinity is detected during a visit.
 */
template<typename Result, typename Visitor, typename... Args>
Result VisitExpression(Visitor *v, const Expression &e, Args &&... args) {
  switch (e.get_kind()) {
    case ExpressionKind::Constant:return v->VisitConstant(e, std::forward<Args>(args)...);

    case ExpressionKind::Var:return v->VisitVariable(e, std::forward<Args>(args)...);

    case ExpressionKind::Add:return v->VisitAddition(e, std::forward<Args>(args)...);

    case ExpressionKind::Mul:return v->VisitMultiplication(e, std::forward<Args>(args)...);

    case ExpressionKind::Div:return v->VisitDivision(e, std::forward<Args>(args)...);

    case ExpressionKind::Log:return v->VisitLog(e, std::forward<Args>(args)...);

    case ExpressionKind::Abs:return v->VisitAbs(e, std::forward<Args>(args)...);

    case ExpressionKind::Exp:return v->VisitExp(e, std::forward<Args>(args)...);

    case ExpressionKind::Sqrt:return v->VisitSqrt(e, std::forward<Args>(args)...);

    case ExpressionKind::Pow:return v->VisitPow(e, std::forward<Args>(args)...);

    case ExpressionKind::Sin:return v->VisitSin(e, std::forward<Args>(args)...);

    case ExpressionKind::Cos:return v->VisitCos(e, std::forward<Args>(args)...);

    case ExpressionKind::Tan:return v->VisitTan(e, std::forward<Args>(args)...);

    case ExpressionKind::Asin:return v->VisitAsin(e, std::forward<Args>(args)...);

    case ExpressionKind::Acos:return v->VisitAcos(e, std::forward<Args>(args)...);

    case ExpressionKind::Atan:return v->VisitAtan(e, std::forward<Args>(args)...);

    case ExpressionKind::Atan2:return v->VisitAtan2(e, std::forward<Args>(args)...);

    case ExpressionKind::Sinh:return v->VisitSinh(e, std::forward<Args>(args)...);

    case ExpressionKind::Cosh:return v->VisitCosh(e, std::forward<Args>(args)...);

    case ExpressionKind::Tanh:return v->VisitTanh(e, std::forward<Args>(args)...);

    case ExpressionKind::Min:return v->VisitMin(e, std::forward<Args>(args)...);

    case ExpressionKind::Max:return v->VisitMax(e, std::forward<Args>(args)...);

    case ExpressionKind::IfThenElse:return v->VisitIfThenElse(e, std::forward<Args>(args)...);

    case ExpressionKind::Infty:throw std::runtime_error("An infinity is detected while visiting an expression.");

    case ExpressionKind::NaN:throw std::runtime_error("NaN is detected while visiting an expression.");

    case ExpressionKind::UninterpretedFunction:return v->VisitUninterpretedFunction(e, std::forward<Args>(args)...);
  }
  // Should not be reachable. But we need the following to avoid "control
  // reaches end of non-void function" gcc-warning.
  throw std::runtime_error("Should not be reachable.");
}

} // namespace dlinear::drake::symbolic


