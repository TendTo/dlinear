/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Base class for visitors of symbolic formulas.
 *
 * The class provides all the methods expected to visit the underlying
 * formula and return a modified version.
 * By default, the visitor returns the original formula, but it can be
 * overridden by the derived classes.
 */
#pragma once

#include <string>

#include "dlinear/symbolic/GenericFormulaVisitor.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"

namespace dlinear {

/**
 * This base class provides all the methods expected to visit the underlying formula and return a modified version.
 *
 * By default, the visitor returns the original formula, but it can be overridden by the derived classes.
 */
template <class... Args>
class FormulaVisitor : public GenericFormulaVisitor<Formula, Args...> {
 protected:
  /**
   * Construct a new FormulaVisitor object with the given @p config.
   * @param config configuration
   * @param class_name name of the subclass
   */
  explicit FormulaVisitor(const Config &config, const std::string &class_name = "FormulaVisitor")
      : GenericFormulaVisitor<Formula, Args...>{config, class_name} {}

  [[nodiscard]] Formula VisitFalse(const Formula &f, Args...) const override { return f; }
  [[nodiscard]] Formula VisitTrue(const Formula &f, Args...) const override { return f; }
  [[nodiscard]] Formula VisitVariable(const Formula &f, Args...) const override { return f; }
  [[nodiscard]] Formula VisitEqualTo(const Formula &f, Args...) const override { return f; }
  [[nodiscard]] Formula VisitNotEqualTo(const Formula &f, Args...) const override { return f; }
  [[nodiscard]] Formula VisitGreaterThan(const Formula &f, Args...) const override { return f; }
  [[nodiscard]] Formula VisitGreaterThanOrEqualTo(const Formula &f, Args...) const override { return f; }
  [[nodiscard]] Formula VisitLessThan(const Formula &f, Args...) const override { return f; }
  [[nodiscard]] Formula VisitLessThanOrEqualTo(const Formula &f, Args...) const override { return f; }
  [[nodiscard]] Formula VisitConjunction(const Formula &f, Args...) const override { return f; }
  [[nodiscard]] Formula VisitDisjunction(const Formula &f, Args...) const override { return f; }
  [[nodiscard]] Formula VisitNegation(const Formula &f, Args...) const override { return f; }
  [[nodiscard]] Formula VisitForall(const Formula &f, Args...) const override { return f; }
};

}  // namespace dlinear
