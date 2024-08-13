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
                               const PredicateAbstractor& pa)
    : ReluConstraint(pa[inactive_formula], pa[active_formula], std::move(relu_var)) {}
ReluConstraint::ReluConstraint(Variable inactive_var, Variable active_var, Variable relu_var)
    : GuidedConstraint({{active_var, true}}),
      lower_bound_{&zero},
      upper_bound_{&Infinity::infinity(Config::LPSolver::SOPLEX)},  // TODO(tend): does it need any other solver?
      inactive_var_{std::move(inactive_var)},
      active_var_{std::move(active_var)},
      relu_var_{std::move(relu_var)} {
  DLINEAR_ASSERT(inactive_var_.get_type() == Variable::Type::BOOLEAN, "inactive_var_ must be boolean");
  DLINEAR_ASSERT(active_var_.get_type() == Variable::Type::BOOLEAN, "active_var_ must be boolean");
  DLINEAR_ASSERT(relu_var_.get_type() == Variable::Type::CONTINUOUS, "relu_var_ must be continuous");
}

void ReluConstraint::SetBounds(const mpq_class& lower_bound, const mpq_class& upper_bound) {
  SetLowerBound(lower_bound);
  SetUpperBound(upper_bound);
}
void ReluConstraint::SetUpperBound(const mpq_class& upper_bound) { upper_bound_ = &upper_bound; }
void ReluConstraint::SetLowerBound(const mpq_class& lower_bound) { lower_bound_ = &lower_bound; }
void ReluConstraint::SetBounds(const mpq_class* const lower_bound, const mpq_class* const upper_bound) {
  SetLowerBound(lower_bound);
  SetUpperBound(upper_bound);
}
void ReluConstraint::SetUpperBound(const mpq_class* const upper_bound) { upper_bound_ = upper_bound; }
void ReluConstraint::SetLowerBound(const mpq_class* const lower_bound) { lower_bound_ = lower_bound; }

LiteralSet ReluConstraint::Assumptions() const {
  if (!fixed()) return {};
  const bool is_inactive = *upper_bound_ == 0;
  return {{inactive_var_, is_inactive}, {active_var_, !is_inactive}};
}

LiteralSet ReluConstraint::LearnedClauses() const {
  if (!fixed()) return {};
  const bool is_inactive = *upper_bound_ == 0;
  return {{inactive_var_, !is_inactive}, {active_var_, is_inactive}};
}

std::ostream& ReluConstraint::Print(std::ostream& os) const {
  os << "ReluConstraint(if " << relu_var_ << " in [0, 0] then " << inactive_var_ << " else " << active_var_ << " ["
     << *lower_bound_ << ", " << *upper_bound_ << "])";
  return os;
}

}  // namespace dlinear
