/**
 * @file GuidedConstraint.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * GuidedConstraint class
 */
#pragma once

#include <istream>
#include <optional>

#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

class GuidedConstraint {
 public:
  explicit GuidedConstraint(std::vector<Literal> enabled_literals = {});
  virtual ~GuidedConstraint() = default;

  virtual std::ostream& Print(std::ostream& os) const = 0;

  [[nodiscard]] virtual LiteralSet Assumptions() const = 0;
  [[nodiscard]] virtual LiteralSet LearnedClauses() const = 0;

  /** @getter{literals that must be enabled to perform the intended scope, guided constraint} */
  [[nodiscard]] const std::vector<Literal>& enabled_literals() const { return enabled_literals_; }

 protected:
  std::vector<Literal> enabled_literals_;
};

std::ostream& operator<<(std::ostream& os, const GuidedConstraint& gc);

}  // namespace dlinear

OSTREAM_FORMATTER(dlinear::GuidedConstraint)
