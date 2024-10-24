/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "LeakyReluConstraint.h"

#include <utility>

#include "dlinear/symbolic/LinearFormulaFlattener.h"
#include "dlinear/util/Infinity.h"
#include "dlinear/util/exception.h"

namespace dlinear {

const mpq_class LeakyReluConstraint::zero{0};

LeakyReluConstraint::LeakyReluConstraint(const Variable& relu_var, const Expression& e, const float alpha,
                                         const PredicateAbstractor& pa)
    : LeakyReluConstraint(pa[LinearFormulaFlattener{pa.config()}.Flatten(relu_var - e == 0)],
                          pa[LinearFormulaFlattener{pa.config()}.Flatten(relu_var - alpha * e == 0)], relu_var,
                          relu_var - e, relu_var - alpha * e) {}
LeakyReluConstraint::LeakyReluConstraint(Variable active_var, Variable inactive_var, Variable relu_var,
                                         Expression active_soi, Expression inactive_soi)
    : PiecewiseLinearConstraint{nullptr,
                                nullptr,
                                std::move(active_var),
                                std::move(inactive_var),
                                relu_var,
                                std::move(active_soi),
                                std::move(inactive_soi)} {}

void LeakyReluConstraint::UpdateLowerBound(const mpq_class* const lower_bound) {
  PiecewiseLinearConstraint::UpdateLowerBound(lower_bound);
  if (*lower_bound > 0) {
    DLINEAR_ASSERT(state_ != PiecewiseConstraintState::INACTIVE, "constraint is already INACTIVE");
    state_ = PiecewiseConstraintState::ACTIVE;
  }
}
void LeakyReluConstraint::UpdateUpperBound(const mpq_class* const upper_bound) {
  PiecewiseLinearConstraint::UpdateUpperBound(upper_bound);
  if (*upper_bound <= 0) {
    DLINEAR_ASSERT(state_ != PiecewiseConstraintState::ACTIVE, "constraint is already ACTIVE");
    state_ = PiecewiseConstraintState::INACTIVE;
  }
}

void LeakyReluConstraint::EnableLiteral(const Variable&) {
  // DLINEAR_ASSERT(inactive_var_.equal_to(var) || active_var_.equal_to(var), "Invalid variable");
}

std::set<LiteralSet> LeakyReluConstraint::TightenBounds(BoundPreprocessor& preprocessor) {
  std::set<LiteralSet> active_explanations;
  std::set<LiteralSet> inactive_explanations;

  const Bound inactive_upper_bound{&zero, LpColBound::U, {inactive_var_, true}, {}};
  const Bound active_lower_bound{&zero, LpColBound::L, {active_var_, true}, {}};
  preprocessor.PropagateBoundsPolynomial({inactive_var_, true}, theory_var_, {inactive_upper_bound},
                                         inactive_explanations);
  preprocessor.PropagateBoundsPolynomial({active_var_, true}, theory_var_, {active_lower_bound}, active_explanations);
  if (!active_explanations.empty() && !inactive_explanations.empty()) {
    return active_explanations;
  }

  DLINEAR_DEV_FMT("Bounds: [{} {}]", preprocessor.theory_bounds().at(theory_var_).active_lower_bound(),
                  preprocessor.theory_bounds().at(theory_var_).active_upper_bound());
  UpdateLowerBound(&preprocessor.theory_bounds().at(theory_var_).active_lower_bound());
  UpdateUpperBound(&preprocessor.theory_bounds().at(theory_var_).active_upper_bound());
  return {};
}

LiteralSet LeakyReluConstraint::Assumptions() const {
  DLINEAR_ASSERT(!fixed(), "LeakyReluConstraint::Assumptions() should not be called on a fixed constraint");
  const bool is_inactive = *upper_bound_ == 0;
  return {{inactive_var_, is_inactive}, {active_var_, !is_inactive}};
}

LiteralSet LeakyReluConstraint::LearnedClauses() const {
  if (fixed()) {
    const bool is_inactive = *upper_bound_ == 0;
    return {{inactive_var_, !is_inactive}, {active_var_, is_inactive}};
  }
  return {};
}

std::ostream& LeakyReluConstraint::Print(std::ostream& os) const {
  os << "LeakyReluConstraint(" << active_var_ << " or " << inactive_var_ << " ["
     << (lower_bound_ ? std::to_string(lower_bound_->get_d()) : "-inf") << ", "
     << (upper_bound_ ? std::to_string(upper_bound_->get_d()) : "+inf") << "])";
  return os;
}

}  // namespace dlinear
