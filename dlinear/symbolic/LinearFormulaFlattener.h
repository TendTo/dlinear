#pragma once

#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"

namespace dlinear {

class LinearFormulaFlattener {
 public:
  explicit LinearFormulaFlattener(const Config& config = {}) : needs_expansion_(config.needs_expansion()) {}
  /**
   * Flatten the given formula.
   * @param formula the formula to flatten.
   * @return the flattened formula.
   */
  const Formula& Flatten(const Formula& formula);

 private:
  void BuildFlatteredFormula(const Expression& lhs, const Expression& rhs, FormulaKind kind);

  const bool needs_expansion_;
  Formula flattered_formula_;
};

}  // namespace dlinear
