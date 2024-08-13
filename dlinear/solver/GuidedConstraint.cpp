/**
 * @file GuidedConstraint.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "GuidedConstraint.h"

#include "dlinear/util/exception.h"

namespace dlinear {

GuidedConstraint::GuidedConstraint(std::vector<Literal> enabled_literals)
    : enabled_literals_{std::move(enabled_literals)} {}

std::ostream& operator<<(std::ostream& os, const GuidedConstraint& gc) { return gc.Print(os); }

}  // namespace dlinear
