/**
 * @file FormulaVisitor.h
 * @author dlinear
 * @date 19 Aug 2023
 * @copyright 2023 dlinear
 * @brief Base class for visitors of symbolic formulas.
 *
 * The class provides all the methods expected to visit the underlying
 * formula and return a modified version.
 * By default, the visitor returns the original formula, but it can be
 * overridden by the derived classes.
 */
#pragma once

#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

class FormulaVisitor {
 protected:
  virtual ~FormulaVisitor() = default;
  virtual Formula Visit(const Formula &f) { return f; }
  virtual Formula VisitFalse(const Formula &f) { return f; }
  virtual Formula VisitTrue(const Formula &f) { return f; }
  virtual Formula VisitVariable(const Formula &f) { return f; }
  virtual Formula VisitEqualTo(const Formula &f) { return f; }
  virtual Formula VisitNotEqualTo(const Formula &f) { return f; }
  virtual Formula VisitGreaterThan(const Formula &f) { return f; }
  virtual Formula VisitGreaterThanOrEqualTo(const Formula &f) { return f; }
  virtual Formula VisitLessThan(const Formula &f) { return f; }
  virtual Formula VisitLessThanOrEqualTo(const Formula &f) { return f; }
  virtual Formula VisitConjunction(const Formula &f) { return f; }
  virtual Formula VisitDisjunction(const Formula &f) { return f; }
  virtual Formula VisitNegation(const Formula &f) { return f; }
  virtual Formula VisitForall(const Formula &f) { return f; }
};

}  // namespace dlinear
