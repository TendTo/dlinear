/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "ReluConstraint.h"

#include <utility>

#include "dlinear/symbolic/LinearFormulaFlattener.h"
#include "dlinear/util/Infinity.h"
#include "dlinear/util/exception.h"

namespace dlinear {

const mpq_class ReluConstraint::zero{0};

ReluConstraint::ReluConstraint(const Variable& relu_var, const Expression& e, const PredicateAbstractor& pa)
    : ReluConstraint(pa[LinearFormulaFlattener{pa.config()}.Flatten(relu_var - e == 0)], pa[relu_var == 0], relu_var,
                     relu_var - e) {}
ReluConstraint::ReluConstraint(Variable active_var, Variable inactive_var, Variable relu_var, Expression active_soi)
    : PiecewiseLinearConstraint{
          &zero, nullptr, std::move(active_var), std::move(inactive_var), relu_var, std::move(active_soi), relu_var} {}

void ReluConstraint::UpdateLowerBound(const mpq_class* const lower_bound) {
  PiecewiseLinearConstraint::UpdateLowerBound(lower_bound);
  if (*lower_bound > 0) {
    DLINEAR_ASSERT(state_ != PiecewiseConstraintState::INACTIVE, "constraint is already INACTIVE");
    state_ = PiecewiseConstraintState::ACTIVE;
  }
}
void ReluConstraint::UpdateUpperBound(const mpq_class* const upper_bound) {
  PiecewiseLinearConstraint::UpdateUpperBound(upper_bound);
  if (*upper_bound <= 0) {
    DLINEAR_ASSERT(state_ != PiecewiseConstraintState::ACTIVE, "constraint is already ACTIVE");
    state_ = PiecewiseConstraintState::INACTIVE;
  }
}

void ReluConstraint::EnableLiteral(const Variable&) {
  // DLINEAR_ASSERT(inactive_var_.equal_to(var) || active_var_.equal_to(var), "Invalid variable");
}

std::set<LiteralSet> ReluConstraint::TightenBounds(BoundPreprocessor& preprocessor) {
  std::set<LiteralSet> explanations;
  preprocessor.PropagateBoundsPolynomial({active_var_, true}, theory_var_, explanations);
  // The active assignment creates a conflict. Fix the constraint to the inactive state.
  if (!explanations.empty()) {
    DLINEAR_DEV_FMT("Failed active because {}", explanations);
    explanations = preprocessor.EnableLiteral({inactive_var_, true});
  }
  // Both active and inactive assignments are unsat. Return the explanation for the latter.
  if (!explanations.empty()) return explanations;

  UpdateLowerBound(&preprocessor.theory_bounds().at(theory_var_).active_lower_bound());
  UpdateUpperBound(&preprocessor.theory_bounds().at(theory_var_).active_upper_bound());
  return {};
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
  os << "ReluConstraint(" << active_var_ << " or " << inactive_var_ << " ["
     << (lower_bound_ ? lower_bound_->get_str() : "-inf") << ", " << (upper_bound_ ? upper_bound_->get_str() : "+inf")
     << "])";
  return os;
}

}  // namespace dlinear
