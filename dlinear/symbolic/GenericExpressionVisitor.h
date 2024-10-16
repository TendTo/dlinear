/**
* @author Ernesto Casablanca (casablancaernesto@gmail.com)
* @copyright 2024 dlinear
* @licence BSD 3-Clause License
* GenericExpressionVisitor class.
*/
#pragma once

#include <stdexcept>

#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Stats.h"

namespace dlinear {

/**
 * Generic expression visitor implementing the visitor pattern.
 *
 * It will iterate over the expression tree and call the appropriate method for each node.
 * @tparam Result return type of each visit method
 * @tparam Args additional arguments to pass to each visit method
 */
template <typename Result, typename... Args>
class GenericExpressionVisitor {
 public:
  /** @getter{statistics, GenericExpressionVisitor} */
  [[nodiscard]] const IterationStats &stats() const { return stats_; }
  /** @getter{configuration, GenericExpressionVisitor} */
  [[nodiscard]] const Config &config() const { return config_; }

 protected:
  explicit GenericExpressionVisitor(const Config &config, const std::string &class_name = "GenericExpressionVisitor")
      : config_{config}, stats_{config.with_timings(), class_name, "Converting"} {}
  virtual ~GenericExpressionVisitor() = default;

  [[nodiscard]] virtual Result VisitExpression(const Expression &e, Args... args) const {
    switch (e.get_kind()) {
      case ExpressionKind::Constant:
        return VisitConstant(e, std::forward<Args>(args)...);
      case ExpressionKind::Var:
        return VisitVariable(e, std::forward<Args>(args)...);
      case ExpressionKind::Add:
        return VisitAddition(e, std::forward<Args>(args)...);
      case ExpressionKind::Mul:
        return VisitMultiplication(e, std::forward<Args>(args)...);
      case ExpressionKind::Div:
        return VisitDivision(e, std::forward<Args>(args)...);
      case ExpressionKind::Log:
        return VisitLog(e, std::forward<Args>(args)...);
      case ExpressionKind::Abs:
        return VisitAbs(e, std::forward<Args>(args)...);
      case ExpressionKind::Exp:
        return VisitExp(e, std::forward<Args>(args)...);
      case ExpressionKind::Sqrt:
        return VisitSqrt(e, std::forward<Args>(args)...);
      case ExpressionKind::Pow:
        return VisitPow(e, std::forward<Args>(args)...);
      case ExpressionKind::Sin:
        return VisitSin(e, std::forward<Args>(args)...);
      case ExpressionKind::Cos:
        return VisitCos(e, std::forward<Args>(args)...);
      case ExpressionKind::Tan:
        return VisitTan(e, std::forward<Args>(args)...);
      case ExpressionKind::Asin:
        return VisitAsin(e, std::forward<Args>(args)...);
      case ExpressionKind::Acos:
        return VisitAcos(e, std::forward<Args>(args)...);
      case ExpressionKind::Atan:
        return VisitAtan(e, std::forward<Args>(args)...);
      case ExpressionKind::Atan2:
        return VisitAtan2(e, std::forward<Args>(args)...);
      case ExpressionKind::Sinh:
        return VisitSinh(e, std::forward<Args>(args)...);
      case ExpressionKind::Cosh:
        return VisitCosh(e, std::forward<Args>(args)...);
      case ExpressionKind::Tanh:
        return VisitTanh(e, std::forward<Args>(args)...);
      case ExpressionKind::Min:
        return VisitMin(e, std::forward<Args>(args)...);
      case ExpressionKind::Max:
        return VisitMax(e, std::forward<Args>(args)...);
      case ExpressionKind::IfThenElse:
        return VisitIfThenElse(e, std::forward<Args>(args)...);
      case ExpressionKind::Infty:
        throw std::runtime_error("An infinity is detected while visiting an expression.");
      case ExpressionKind::NaN:
        throw std::runtime_error("NaN is detected while visiting an expression.");
      case ExpressionKind::UninterpretedFunction:
        return VisitUninterpretedFunction(e, std::forward<Args>(args)...);
      default:
        throw std::runtime_error("Unreachable code.");
    }
  }

  virtual Result VisitVariable(const Expression &e, Args... args) const = 0;
  virtual Result VisitConstant(const Expression &e, Args... args) const = 0;
  virtual Result VisitAddition(const Expression &e, Args... args) const = 0;
  virtual Result VisitMultiplication(const Expression &e, Args... args) const = 0;
  virtual Result VisitDivision(const Expression &e, Args... args) const = 0;
  virtual Result VisitLog(const Expression &e, Args... args) const = 0;
  virtual Result VisitAbs(const Expression &e, Args... args) const = 0;
  virtual Result VisitExp(const Expression &e, Args... args) const = 0;
  virtual Result VisitSqrt(const Expression &e, Args... args) const = 0;
  virtual Result VisitPow(const Expression &e, Args... args) const = 0;
  virtual Result VisitSin(const Expression &e, Args... args) const = 0;
  virtual Result VisitCos(const Expression &e, Args... args) const = 0;
  virtual Result VisitTan(const Expression &e, Args... args) const = 0;
  virtual Result VisitAsin(const Expression &e, Args... args) const = 0;
  virtual Result VisitAcos(const Expression &e, Args... args) const = 0;
  virtual Result VisitAtan(const Expression &e, Args... args) const = 0;
  virtual Result VisitAtan2(const Expression &e, Args... args) const = 0;
  virtual Result VisitSinh(const Expression &e, Args... args) const = 0;
  virtual Result VisitCosh(const Expression &e, Args... args) const = 0;
  virtual Result VisitTanh(const Expression &e, Args... args) const = 0;
  virtual Result VisitMin(const Expression &e, Args... args) const = 0;
  virtual Result VisitMax(const Expression &e, Args... args) const = 0;
  virtual Result VisitIfThenElse(const Expression &e, Args... args) const = 0;
  virtual Result VisitUninterpretedFunction(const Expression &e, Args... args) const = 0;

  const Config &config_;          ///< Configuration
  mutable IterationStats stats_;  ///< Statistics
};

}  // namespace dlinear
