/**
 * @file TheorySolverBoundVector.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "TheorySolverBoundVector.h"

#include <algorithm>
#include <utility>

#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

#define TRACE_VIOLATED_BOUNDS(it)                                                                                  \
  DLINEAR_TRACE_FMT("TheorySolverBoundVector::ViolatedBounds: ({} {}) incompatible with ({} {})", value, lp_bound, \
                    *std::get<0>(*it), std::get<1>(*it))

namespace dlinear {

#define FindLowerBoundValue(value_ptr) bounds_.lower_bound({value_ptr, LpColBound::L, 0})
#define FindLowerBound(value_ptr, bound) bounds_.lower_bound({value_ptr, bound, 0})
#define FindUpperBoundValue(value_ptr) bounds_.upper_bound({value_ptr, LpColBound::U, 0})
#define FindUpperBound(value_ptr, bound) bounds_.upper_bound({value_ptr, bound, 0})
#define FindLowerNqBoundValue(value_ptr) nq_bounds_.lower_bound({value_ptr, LpColBound::D, 0})
#define FindUpperNqBoundValue(value_ptr) nq_bounds_.upper_bound({value_ptr, LpColBound::D, 0})

bool BoundComparator::operator()(const TheorySolverBoundVector::Bound& lhs,
                                 const TheorySolverBoundVector::Bound& rhs) const {
  const auto& [value_l, type_l, idx_l] = lhs;
  const auto& [value_r, type_r, idx_r] = rhs;
  if (*value_l < *value_r) return true;
  if (*value_l > *value_r) return false;
  return type_l < type_r;
}

TheorySolverBoundVector::TheorySolverBoundVector(const mpq_class& inf_l, const mpq_class& inf_u)
    : n_lower_bounds_{0},
      bounds_{},
      nq_bounds_{},
      inf_l_{&inf_l},
      inf_u_{&inf_u},
      active_lower_bound_{inf_l_},
      active_upper_bound_{inf_u_} {}

TheorySolverBoundVector::BoundIterator TheorySolverBoundVector::AddBound(const mpq_class& value, LpColBound lp_bound,
                                                                         const int idx) {
  DLINEAR_ASSERT_FMT(lp_bound == LpColBound::L || lp_bound == LpColBound::U || lp_bound == LpColBound::B ||
                         lp_bound == LpColBound::SL || lp_bound == LpColBound::SU || lp_bound == LpColBound::D,
                     "Valid must be L, U, B, SL, SU or D. Received: {}", lp_bound);
  const BoundIterator violation{ViolatedBounds(value, lp_bound)};
  if (!violation.empty()) return violation;

  // Add the new lp_bound
  auto it = bounds_.end();
  switch (lp_bound) {
    case LpColBound::SL:
    case LpColBound::L:
      ++n_lower_bounds_;
      it = bounds_.emplace(&value, lp_bound, idx);
      break;
    case LpColBound::SU:
    case LpColBound::U:
      it = bounds_.emplace(false, &value, lp_bound, idx);
      break;
    case LpColBound::B:
      // Check if adding this lp_bound will cause a violation
      if (ViolatedNqBounds(value, value))
        return {bounds_.cend(), bounds_.cend(), FindLowerNqBoundValue(&value), FindUpperNqBoundValue(&value)};
      ++n_lower_bounds_;
      active_lower_bound_ = active_upper_bound_ = &value;
      bounds_.emplace(false, &value, LpColBound::L, idx);
      bounds_.emplace(&value, LpColBound::U, idx);
      return {};
    case LpColBound::D:
      if (IsActiveEquality(value)) return {FindLowerBoundValue(&value), FindUpperBoundValue(&value)};
      nq_bounds_.emplace(&value, lp_bound, idx);
      return {};
    default:
      break;
  }

  bool changed_active_bounds = false;
  const mpq_class* backup_active_lower_bound = active_lower_bound_;
  const mpq_class* backup_active_upper_bound = active_upper_bound_;
  // Check if there has been a change in the active bounds
  if ((lp_bound == LpColBound::L || lp_bound == LpColBound::SL) && value > *active_lower_bound_) {
    active_lower_bound_ = &value;
    changed_active_bounds = true;
  } else if ((lp_bound == LpColBound::U || lp_bound == LpColBound::SU) && value < *active_upper_bound_) {
    active_upper_bound_ = &value;
    changed_active_bounds = true;
  }

  if (changed_active_bounds) {
    if (ViolatedNqBounds()) {
      bounds_.erase(it);
      if (lp_bound == LpColBound::L || lp_bound == LpColBound::SL) --n_lower_bounds_;
      const BoundIterator nq_violation{
          FindLowerBoundValue(active_lower_bound_), FindUpperBoundValue(active_upper_bound_),
          FindLowerNqBoundValue(active_lower_bound_), FindUpperNqBoundValue(active_upper_bound_)};
      active_lower_bound_ = backup_active_lower_bound;
      active_upper_bound_ = backup_active_upper_bound;
      return nq_violation;
    }
  }

  return {};
}

TheorySolverBoundVector::BoundIterator TheorySolverBoundVector::ViolatedBounds(const mpq_class& value,
                                                                               LpColBound lp_bound) const {
  if (lp_bound == LpColBound::D) return {};
  DLINEAR_ASSERT_FMT(lp_bound == LpColBound::L || lp_bound == LpColBound::U || lp_bound == LpColBound::B ||
                         lp_bound == LpColBound::SL || lp_bound == LpColBound::SU,
                     "Valid must be L, U, B, SL or SU. Received: {}", lp_bound);

  DLINEAR_TRACE_FMT("TheorySolverBoundVector::ViolatedBounds: checking ({} {})", value, lp_bound);
  auto it = bounds_.cend();

  switch (lp_bound) {
    case LpColBound::SL:
    case LpColBound::L:
      if (value > *active_upper_bound_) return {LowerBoundEnd(), FindUpperBound(&value, !lp_bound)};
      it = bounds_.upper_bound({&value, lp_bound, 0});
      if (it == bounds_.cend() || *std::get<0>(*it) != value) return {};
      if (lp_bound == LpColBound::L && std::get<1>(*it) != LpColBound::SU) return {};
      TRACE_VIOLATED_BOUNDS(it);
      DLINEAR_ASSERT(LowerBoundEnd() < FindUpperBound(&value, !lp_bound), "Bounds must not be inverted");
      return {LowerBoundEnd(), FindUpperBound(&value, !lp_bound)};
    case LpColBound::SU:
    case LpColBound::U:
      if (value < *active_lower_bound_) return {FindLowerBound(&value, !lp_bound), LowerBoundEnd()};
      it = bounds_.lower_bound({&value, lp_bound, 0});
      if (it == bounds_.cbegin() || *std::get<0>(*(it - 1)) != value) return {};
      if (lp_bound == LpColBound::U && std::get<1>(*(it - 1)) != LpColBound::SL) return {};
      TRACE_VIOLATED_BOUNDS((it - 1));
      DLINEAR_ASSERT(FindLowerBound(&value, !lp_bound) < LowerBoundEnd(), "Bounds must not be inverted");
      return {FindLowerBound(&value, !lp_bound), LowerBoundEnd()};
    case LpColBound::B:
      if (value < *active_lower_bound_) return {FindLowerBound(&value, LpColBound::SL), LowerBoundEnd()};
      if (value > *active_upper_bound_) return {LowerBoundEnd(), FindUpperBound(&value, LpColBound::SU)};
      it = bounds_.upper_bound({&value, LpColBound::L, 0});
      if ((it != bounds_.cend() && *std::get<0>(*it) == value && std::get<1>(*it) == LpColBound::SU)) {
        TRACE_VIOLATED_BOUNDS(it);
        DLINEAR_ASSERT(LowerBoundEnd() < FindUpperBoundValue(&value), "Bounds must not be inverted");
        return {LowerBoundEnd(), FindUpperBoundValue(&value)};
      }
      it = bounds_.lower_bound({&value, LpColBound::U, 0});
      if ((it != bounds_.cbegin() && *std::get<0>(*(it - 1)) == value && std::get<1>(*(it - 1)) == LpColBound::SL)) {
        TRACE_VIOLATED_BOUNDS((it - 1));
        DLINEAR_ASSERT(FindLowerBoundValue(&value) < LowerBoundEnd(), "Bounds must not be inverted");
        return {FindLowerBoundValue(&value), LowerBoundEnd()};
      }
      return {};
    default:
      DLINEAR_UNREACHABLE();
  }
}

bool TheorySolverBoundVector::ViolatedNqBounds() const {
  if (active_upper_bound_ != active_lower_bound_) return false;
  // The active bounds are equal, verify whether they are violated
  auto nq_value_it = nq_bounds_.find({active_upper_bound_, LpColBound::D, 0});
  // No violation, return
  if (nq_value_it == nq_bounds_.end()) return false;
  // Violated strict bound, remove the last added bound and return the interval
  return true;
}

bool TheorySolverBoundVector::ViolatedNqBounds(const mpq_class& lb, const mpq_class& ub) const {
  if (lb != ub) return false;
  // The active bounds are equal, verify whether they are violated
  auto nq_value_it = nq_bounds_.find({&lb, LpColBound::D, 0});
  // No violation, return
  if (nq_value_it == nq_bounds_.end()) return false;
  // Violated strict bound, remove the last added bound and return the interval
  return true;
}

void TheorySolverBoundVector::Clear() {
  bounds_.clear();
  n_lower_bounds_ = 0;
  nq_bounds_.clear();
  active_lower_bound_ = inf_l_;
  active_upper_bound_ = inf_u_;
}

bool TheorySolverBoundVector::IsActiveEquality(const mpq_class& value) const {
  if (n_lower_bounds_ == 0 || n_lower_bounds_ == static_cast<int>(bounds_.size())) return false;
  return *active_upper_bound_ == *active_lower_bound_ && *active_upper_bound_ == value;
}

bool TheorySolverBoundVector::IsLowerBound(const mpq_class& value) const {
  auto it = bounds_.find({&value, LpColBound::L, 0});
  if (it != bounds_.cend()) return true;
  it = bounds_.find({&value, LpColBound::SL, 0});
  return it != bounds_.cend();
}

bool TheorySolverBoundVector::IsUpperBound(const mpq_class& value) const {
  auto it = bounds_.find({&value, LpColBound::U, 0});
  if (it != bounds_.cend()) return true;
  it = bounds_.find({&value, LpColBound::SU, 0});
  return it != bounds_.cend();
}

TheorySolverBoundVector::BoundIterator TheorySolverBoundVector::active_bounds() const {
  const auto lb = FindLowerBoundValue(active_lower_bound_);
  const auto ub = FindUpperBoundValue(active_upper_bound_);
  // The active bounds are empty or span the entire bounds_ vector
  if (lb == bounds_.cend() || ub == bounds_.cbegin() || lb == ub)
    return {lb, ub, FindLowerNqBoundValue(active_lower_bound_), FindUpperNqBoundValue(active_upper_bound_)};
  const auto& [value_lb, type_lb, idx_lb] = *lb;
  const auto& [value_ub, type_ub, idx_ub] = *(ub - 1);
  // The bounds contains only one type of bound or span across mutiple values. There is no equality bound
  if (type_lb != LpColBound::L || type_ub != LpColBound::U || value_lb != value_ub)
    return {lb, ub, FindLowerNqBoundValue(active_lower_bound_), FindUpperNqBoundValue(active_upper_bound_)};

  auto it = lb;
  auto [value, type, idx] = *it;
  for (; type != type_ub; ++it, type = std::get<1>(*it), idx = std::get<2>(*it)) {
    if (idx == idx_ub)
      return {it, ub, FindLowerNqBoundValue(active_lower_bound_), FindUpperNqBoundValue(active_upper_bound_)};
  }
  it = ub - 1;
  type = std::get<1>(*it);
  idx = std::get<2>(*it);
  for (; type != type_lb; --it, type = std::get<1>(*it), idx = std::get<2>(*it)) {
    if (idx == idx_lb)
      return {lb, it + 1, FindLowerNqBoundValue(active_lower_bound_), FindUpperNqBoundValue(active_upper_bound_)};
  }
  return {lb, ub, FindLowerNqBoundValue(active_lower_bound_), FindUpperNqBoundValue(active_upper_bound_)};
}

std::pair<mpq_class, mpq_class> TheorySolverBoundVector::active_bound_value() const {
  return {*active_lower_bound_, *active_upper_bound_};
}

void TheorySolverBoundVector::SetLowerBound(const mpq_class& value) {
  if (value > *active_upper_bound_)
    DLINEAR_RUNTIME_ERROR_FMT("Upper bound must be greater or equal to lower bound. Lower: {}, Upper: {}",
                              *active_lower_bound_, *active_upper_bound_);
  if (value > *active_lower_bound_) active_lower_bound_ = &value;
}
void TheorySolverBoundVector::SetUpperBound(const mpq_class& value) {
  if (value < *active_lower_bound_)
    DLINEAR_RUNTIME_ERROR_FMT("Upper bound must be greater or equal to lower bound. Lower: {}, Upper: {}",
                              *active_lower_bound_, *active_upper_bound_);
  if (value < *active_upper_bound_) active_upper_bound_ = &value;
}
void TheorySolverBoundVector::SetBounds(const mpq_class& lb, const mpq_class& ub) {
  if (ub < std::max(lb, *active_lower_bound_) || lb > std::min(ub, *active_upper_bound_))
    DLINEAR_RUNTIME_ERROR_FMT("Upper bound must be greater or equal to lower bound. Lower: {}, Upper: {}",
                              *active_lower_bound_, *active_upper_bound_);
  if (lb > *active_lower_bound_) active_lower_bound_ = &lb;
  if (ub < *active_upper_bound_) active_upper_bound_ = &ub;
}

std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector& bounds_vector) {
  os << "TheorySolverBoundVector[" << bounds_vector.active_lower_bound() << "," << bounds_vector.active_upper_bound()
     << "]{ ";
  for (const auto& [value, type, row_idx] : bounds_vector.bounds()) {
    os << "row " << row_idx << ": " << *value << "( " << type << " ), ";
  }
  os << "}";
  return os;
}
std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector::Bound& bound) {
  const auto& [value, type, idx] = bound;
  return os << "Bound{ " << *value << ", " << type << ", " << idx << " }";
}
std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVectorMap& bounds_vector_map) {
  os << "TheorySolverBoundVectorMap{ ";
  for (const auto& [col, bounds_vector] : bounds_vector_map) {
    os << "id " << col << ": " << bounds_vector << ", ";
  }
  os << "}";
  return os;
}
std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVectorVector& bounds_vector_map) {
  os << "TheorySolverBoundVectorVector{ ";
  for (const auto& bounds_vector : bounds_vector_map) {
    os << bounds_vector << ", ";
  }
  os << "}";
  return os;
}

}  // namespace dlinear
