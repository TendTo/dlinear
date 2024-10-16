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
 * Generic formula visitor implementing the visitor pattern.
 *
 * It will iterate over the formula tree and call the appropriate method for each node.
 * @tparam Result return type of each visit method
 * @tparam Args additional arguments to pass to each visit method
 */
template <class Result, class... Args>
class GenericFormulaVisitor {
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
  explicit GenericFormulaVisitor(const Config &config, const std::string &class_name = "GenericFormulaVisitor")
      : config_{config}, stats_{config.with_timings(), class_name, "Converting"} {}
  virtual ~GenericFormulaVisitor() = default;

  [[nodiscard]] virtual Result VisitFormula(const Formula &f, Args... args) const {
    switch (f.get_kind()) {
      case FormulaKind::False:
        return VisitFalse(f, args...);
      case FormulaKind::True:
        return VisitTrue(f, args...);
      case FormulaKind::Var:
        return VisitVariable(f, args...);
      case FormulaKind::Eq:
        return VisitEqualTo(f, args...);
      case FormulaKind::Neq:
        return VisitNotEqualTo(f, args...);
      case FormulaKind::Gt:
        return VisitGreaterThan(f, args...);
      case FormulaKind::Geq:
        return VisitGreaterThanOrEqualTo(f, args...);
      case FormulaKind::Lt:
        return VisitLessThan(f, args...);
      case FormulaKind::Leq:
        return VisitLessThanOrEqualTo(f, args...);
      case FormulaKind::And:
        return VisitConjunction(f, args...);
      case FormulaKind::Or:
        return VisitDisjunction(f, args...);
      case FormulaKind::Not:
        return VisitNegation(f, args...);
      case FormulaKind::Forall:
        return VisitForall(f, args...);
      default:
        throw std::runtime_error("Unknown formula kind");
    }
  }
  [[nodiscard]] virtual Result VisitFalse(const Formula &f, Args... args) const = 0;
  [[nodiscard]] virtual Result VisitTrue(const Formula &f, Args... args) const = 0;
  [[nodiscard]] virtual Result VisitVariable(const Formula &f, Args... args) const = 0;
  [[nodiscard]] virtual Result VisitEqualTo(const Formula &f, Args... args) const = 0;
  [[nodiscard]] virtual Result VisitNotEqualTo(const Formula &f, Args... args) const = 0;
  [[nodiscard]] virtual Result VisitGreaterThan(const Formula &f, Args... args) const = 0;
  [[nodiscard]] virtual Result VisitGreaterThanOrEqualTo(const Formula &f, Args... args) const = 0;
  [[nodiscard]] virtual Result VisitLessThan(const Formula &f, Args... args) const = 0;
  [[nodiscard]] virtual Result VisitLessThanOrEqualTo(const Formula &f, Args... args) const = 0;
  [[nodiscard]] virtual Result VisitConjunction(const Formula &f, Args... args) const = 0;
  [[nodiscard]] virtual Result VisitDisjunction(const Formula &f, Args... args) const = 0;
  [[nodiscard]] virtual Result VisitNegation(const Formula &f, Args... args) const = 0;
  [[nodiscard]] virtual Result VisitForall(const Formula &f, Args... args) const = 0;

  const Config &config_;          ///< Configuration.
  mutable IterationStats stats_;  ///< Statistics.
};

}  // namespace dlinear
