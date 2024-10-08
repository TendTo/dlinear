/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "dlinear/solver/PiecewiseLinearConstraint.h"

#include "dlinear/util/Config.h"
#include "dlinear/util/Infinity.h"
#include "dlinear/util/exception.h"

namespace dlinear {

const Expression PiecewiseLinearConstraint::zero_soi{0};

PiecewiseLinearConstraint::PiecewiseLinearConstraint(const mpq_class* const lb, const mpq_class* const ub,
                                                     Variable active_var, Variable inactive_var, Variable theory_var,
                                                     Expression active_soi, Expression inactive_soi,
                                                     PiecewiseConstraintState state)
    : lower_bound_{lb},
      upper_bound_{ub},
      active_var_{std::move(active_var)},
      inactive_var_{std::move(inactive_var)},
      theory_var_{std::move(theory_var)},
      active_soi_{std::move(active_soi)},
      inactive_soi_{std::move(inactive_soi)},
      state_{state} {
  DLINEAR_ASSERT(!active_var_.is_dummy(), "active_var_ must be valid");
  DLINEAR_ASSERT(!inactive_var_.is_dummy(), "inactive_var_ must be valid");
  DLINEAR_ASSERT(!theory_var_.is_dummy(), "theory_var_ must be valid");
  DLINEAR_ASSERT(active_var_.get_type() == Variable::Type::BOOLEAN, "active_var_ must be boolean");
  DLINEAR_ASSERT(inactive_var_.get_type() == Variable::Type::BOOLEAN, "inactive_var_ must be boolean");
  DLINEAR_ASSERT(theory_var_.get_type() == Variable::Type::CONTINUOUS, "theory_var_ must be continuous");
}

const mpq_class& PiecewiseLinearConstraint::lower_bound() const {
  return lower_bound_ == nullptr ? Infinity::ninfinity(Config::LPSolver::SOPLEX) : *lower_bound_;
}
const mpq_class& PiecewiseLinearConstraint::upper_bound() const {
  return upper_bound_ == nullptr ? Infinity::infinity(Config::LPSolver::SOPLEX) : *upper_bound_;
}

const Expression& PiecewiseLinearConstraint::soi() const {
  switch (state_) {
    case PiecewiseConstraintState::ACTIVE:
      return active_soi_;
    case PiecewiseConstraintState::INACTIVE:
      return inactive_soi_;
    default:
      return zero_soi;
  }
}

void PiecewiseLinearConstraint::UpdateBounds(const mpq_class& lb, const mpq_class& ub) {
  DLINEAR_ASSERT(lb <= ub, "Invalid bounds");
  UpdateLowerBound(&lb);
  UpdateUpperBound(&ub);
}
void PiecewiseLinearConstraint::UpdateBounds(const mpq_class* lb, const mpq_class* ub) {
  DLINEAR_ASSERT(lb == nullptr || ub == nullptr || *lb <= *ub, "Invalid bounds");
  if (lb != nullptr) UpdateLowerBound(lb);
  if (ub != nullptr) UpdateUpperBound(ub);
}
void PiecewiseLinearConstraint::UpdateLowerBound(const mpq_class* lb) {
  DLINEAR_ASSERT(lb != nullptr, "Invalid lower bound");
  DLINEAR_ASSERT_FMT(upper_bound_ == nullptr || *lb <= *upper_bound_,
                     "New lower bound must be less than or equal to the upper bound. Got {} > {}", *lb, *upper_bound_);
  if (lower_bound_ == nullptr || *lb > *lower_bound_) lower_bound_ = lb;
}
void PiecewiseLinearConstraint::UpdateUpperBound(const mpq_class* ub) {
  DLINEAR_ASSERT(ub != nullptr, "Invalid upper bound");
  DLINEAR_ASSERT_FMT(lower_bound_ == nullptr || *ub >= *lower_bound_,
                     "New upper bound must be greater than or equal to the lower bound. Got {} < {}", *ub,
                     *lower_bound_);
  if (upper_bound_ == nullptr || *ub < *upper_bound_) upper_bound_ = ub;
}
mpq_class PiecewiseLinearConstraint::Cost(const Environment& env) const {
  switch (state_) {
    case PiecewiseConstraintState::ACTIVE:
      return active_soi_.Evaluate(env);
    case PiecewiseConstraintState::INACTIVE:
      return inactive_soi_.Evaluate(env);
    default:
      return 0;
  }
}
mpq_class PiecewiseLinearConstraint::Cost(const Environment& env, const bool active) const {
  return (active ? active_soi_ : inactive_soi_).Evaluate(env);
}

std::ostream& operator<<(std::ostream& os, const PiecewiseLinearConstraint& gc) { return gc.Print(os); }

}  // namespace dlinear
