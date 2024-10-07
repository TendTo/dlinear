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

#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Stats.h"

namespace dlinear {
/**
 * This base class provides all the methods expected to visit the underlying formula and return a modified version.
 * By default, the visitor returns the original formula, but it can be overridden by the derived classes.
 */
class FormulaVisitor {
 public:
  /** @getter{statistics, FormulaVisitor} */
  [[nodiscard]] const IterationStats &stats() const { return stats_; }
  /** @getter{configuration, FormulaVisitor} */
  [[nodiscard]] const Config &config() const { return config_; }

 protected:
  /**
   * Construct a new FormulaVisitor object with the given @p config.
   * @param config configuration
   * @param class_name name of the subclass
   */
  explicit FormulaVisitor(const Config &config, const std::string &class_name = "FormulaVisitor")
      : config_{config}, stats_{config.with_timings(), class_name, "Converting"} {}
  virtual ~FormulaVisitor() = default;
  [[nodiscard]] virtual Formula Visit(const Formula &f);
  [[nodiscard]] virtual Formula VisitFalse(const Formula &f) { return f; }
  [[nodiscard]] virtual Formula VisitTrue(const Formula &f) { return f; }
  [[nodiscard]] virtual Formula VisitVariable(const Formula &f) { return f; }
  [[nodiscard]] virtual Formula VisitEqualTo(const Formula &f) { return f; }
  [[nodiscard]] virtual Formula VisitNotEqualTo(const Formula &f) { return f; }
  [[nodiscard]] virtual Formula VisitGreaterThan(const Formula &f) { return f; }
  [[nodiscard]] virtual Formula VisitGreaterThanOrEqualTo(const Formula &f) { return f; }
  [[nodiscard]] virtual Formula VisitLessThan(const Formula &f) { return f; }
  [[nodiscard]] virtual Formula VisitLessThanOrEqualTo(const Formula &f) { return f; }
  [[nodiscard]] virtual Formula VisitConjunction(const Formula &f) { return f; }
  [[nodiscard]] virtual Formula VisitDisjunction(const Formula &f) { return f; }
  [[nodiscard]] virtual Formula VisitNegation(const Formula &f) { return f; }
  [[nodiscard]] virtual Formula VisitForall(const Formula &f) { return f; }

  const Config &config_;  ///< Configuration.
  IterationStats stats_;  ///< Statistics.
};

}  // namespace dlinear
