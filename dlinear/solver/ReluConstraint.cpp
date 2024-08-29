/**
 * @file ReluConstraint.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * ReluConstraint class
 */
#include "ReluConstraint.h"

#include <utility>

#include "dlinear/util/Infinity.h"

namespace dlinear {

const mpq_class ReluConstraint::zero{0};

ReluConstraint::ReluConstraint(const Formula& inactive_formula, const Formula& active_formula, Variable relu_var,
                               Expression active_soi, const PredicateAbstractor& pa)
    : ReluConstraint(pa[inactive_formula], pa[active_formula], std::move(relu_var), std::move(active_soi)) {}
ReluConstraint::ReluConstraint(Variable active_var, Variable inactive_var, Variable theory_var, Expression active_soi)
    : PiecewiseLinearConstraint{
          &zero,     nullptr, std::move(active_var), std::move(inactive_var), theory_var, std::move(active_soi),
          theory_var} {}

void ReluConstraint::UpdateLowerBound(const mpq_class* const lower_bound) {
  PiecewiseLinearConstraint::UpdateLowerBound(lower_bound);
  if (*lower_bound > 0) state_ = PiecewiseConstraintState::FIXED;
}
void ReluConstraint::UpdateUpperBound(const mpq_class* const upper_bound) {
  PiecewiseLinearConstraint::UpdateUpperBound(upper_bound);
  if (*upper_bound <= 0) state_ = PiecewiseConstraintState::FIXED;
}

void ReluConstraint::EnableLiteral(const Variable& var) {
  DLINEAR_ASSERT(inactive_var_.equal_to(var) || active_var_.equal_to(var), "Invalid variable");
}

LiteralSet ReluConstraint::Assumptions() const {
  DLINEAR_ASSERT(!fixed(), "ReluConstraint::Assumptions() should not be called on a fixed constraint");
  const bool is_inactive = *upper_bound_ == 0;
  return {{inactive_var_, is_inactive}, {active_var_, !is_inactive}};
}

LiteralSet ReluConstraint::LearnedClauses() const {
  if (fixed()) {
    const bool is_inactive = *upper_bound_ == 0;
    return {{inactive_var_, !is_inactive}, {active_var_, is_inactive}};
  }
  return {};
}

std::ostream& ReluConstraint::Print(std::ostream& os) const {
  os << "ReluConstraint(" << theory_var_ << " = " << active_var_ << " if " << active_var_ << " ["
     << *lower_bound_ << ", " << *upper_bound_ << "])";
  return os;
}

}  // namespace dlinear
