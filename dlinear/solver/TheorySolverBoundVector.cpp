/**
 * @file TheorySolverBoundVector.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "TheorySolverBoundVector.h"

#include <utility>

namespace std {

bool less<std::pair<mpq_class, ::dlinear::Literal>>::operator()(
    const std::pair<mpq_class, ::dlinear::Literal>& lhs, const std::pair<mpq_class, ::dlinear::Literal>& rhs) const {
  return lhs.first < rhs.first;
}
}  // namespace std

namespace dlinear {

const Literal TheorySolverBoundVector::default_lit_{};

TheorySolverBoundVector::TheorySolverBoundVector(mpq_class inf)
    : n_lower_bounds_{0},
      bounds_{},
      nq_values_{},
      active_lower_bound_{-inf},
      active_upper_bound_{inf},
      inf_l_{-inf},
      inf_u_{std::move(inf)} {}

TheorySolverBoundVector::TheorySolverBoundVector(mpq_class inf_l, mpq_class inf_u)
    : n_lower_bounds_{0},
      bounds_{},
      nq_values_{},
      active_lower_bound_{inf_l},
      active_upper_bound_{inf_u},
      inf_l_{std::move(inf_l)},
      inf_u_{std::move(inf_u)} {}

std::optional<TheorySolverBoundVector::Violation> TheorySolverBoundVector::AddBound(const mpq_class& value,
                                                                                    LpColBound bound,
                                                                                    const Literal& lit) {
  DLINEAR_ASSERT_FMT(bound == LpColBound::L || bound == LpColBound::U || bound == LpColBound::B ||
                         bound == LpColBound::SL || bound == LpColBound::SU || bound == LpColBound::D,
                     "Valid must be L, U, B, SL, SU or D. Received: {}", bound);
  const std::optional<Violation> violation{ViolatedBounds(value, bound)};
  if (violation.has_value()) return violation;

  // Add the new bound
  long distance = -2;
  auto it = bounds_.end();
  switch (bound) {
    case LpColBound::SL:
    case LpColBound::L:
      ++n_lower_bounds_;
      it = bounds_.emplace(value, lit);
      distance = std::distance(bounds_.cbegin(), bounds_.lower_bound({value, default_lit_}));
      break;
    case LpColBound::SU:
    case LpColBound::U:
      it = bounds_.emplace(value, lit);
      distance = std::distance(bounds_.cbegin(), bounds_.upper_bound({value, default_lit_}) - 1);
      break;
    case LpColBound::B:
      // Check if adding this bound will cause a violation
      active_upper_bound_ = active_lower_bound_ = value;
      if (ViolatedStrictBounds())
        return {{bounds_.lower_bound({value, default_lit_}), bounds_.upper_bound({value, default_lit_})}};
      ++n_lower_bounds_;
      bounds_.emplace(value, lit);
      bounds_.emplace(value, lit);
      break;
    default:
      break;
  }

  bool changed_active_bounds = false;
  // Check if there has been a change in the active bounds
  if (distance == n_lower_bounds_ - 1 && value > active_lower_bound_) {
    active_lower_bound_ = value;
    changed_active_bounds = true;
  } else if (distance == n_lower_bounds_ && value < active_upper_bound_) {
    active_upper_bound_ = value;
    changed_active_bounds = true;
  }

  if (changed_active_bounds) {
    if (ViolatedStrictBounds()) {
      bounds_.erase(it);
      if (bound == LpColBound::L || bound == LpColBound::SL) --n_lower_bounds_;
      return {{bounds_.lower_bound({active_upper_bound_, default_lit_}),
               bounds_.upper_bound({active_upper_bound_, default_lit_})}};
    }
  }

  // TODO: strict violation could be even stricter by avoiding taking into account same-sense bounds.
  //  This can be done by the TheorySolver

  // A new strict bound has been added, verify whether it has caused a violation
  if (bound == LpColBound::SL || bound == LpColBound::SU || bound == LpColBound::D) {
    // Violated strict bound, remove the last added bound and return the interval
    if (IsActiveEquality(value)) {
      bounds_.erase(it);
      if (bound == LpColBound::SL) --n_lower_bounds_;
      return {{bounds_.lower_bound({value, default_lit_}), bounds_.upper_bound({value, default_lit_})}};
    }
    nq_values_.insert(value);
  }

  return std::nullopt;
}

std::optional<TheorySolverBoundVector::Violation> TheorySolverBoundVector::ViolatedBounds(const mpq_class& value,
                                                                                          LpColBound bound) const {
  if (bound == LpColBound::D) return std::nullopt;

  DLINEAR_ASSERT_FMT(bound == LpColBound::L || bound == LpColBound::U || bound == LpColBound::B ||
                         bound == LpColBound::SL || bound == LpColBound::SU,
                     "Valid must be L, U, B, SL or SU. Received: {}", bound);

  const Bound element{value, default_lit_};
  long insert_position = 0;
  switch (bound) {
    case LpColBound::SL:
    case LpColBound::L:
      insert_position = std::distance(bounds_.cbegin(), bounds_.lower_bound(element));
      DLINEAR_TRACE_FMT("ViolatedBounds: insert_position = {} | ({} {})", insert_position, value, bound);
      if (insert_position <= n_lower_bounds_) return std::nullopt;
      DLINEAR_ASSERT(bounds_.cbegin() + n_lower_bounds_ < bounds_.lower_bound(element), "Bounds must not be inverted");
      return {{bounds_.cbegin() + n_lower_bounds_, bounds_.lower_bound(element)}};
    case LpColBound::SU:
    case LpColBound::U:
      insert_position = std::distance(bounds_.cbegin(), bounds_.upper_bound(element));
      DLINEAR_TRACE_FMT("ViolatedBounds: insert_position = {} | ({} {})", insert_position, value, bound);
      if (insert_position >= n_lower_bounds_) return std::nullopt;
      DLINEAR_ASSERT(bounds_.upper_bound(element) < bounds_.cbegin() + n_lower_bounds_, "Bounds must not be inverted");
      return {{bounds_.upper_bound(element), bounds_.cbegin() + n_lower_bounds_}};
    case LpColBound::B:
      insert_position = std::distance(bounds_.cbegin(), bounds_.lower_bound(element));
      DLINEAR_TRACE_FMT("ViolatedBounds: insert_position = {} | ({} {})", insert_position, value, bound);
      if (insert_position > n_lower_bounds_)
        return {{bounds_.cbegin() + n_lower_bounds_, bounds_.lower_bound(element)}};
      insert_position = std::distance(bounds_.cbegin(), bounds_.upper_bound(element));
      DLINEAR_TRACE_FMT("ViolatedBounds: insert_position = {} | ({} {})", insert_position, value, bound);
      if (insert_position < n_lower_bounds_)
        return {{bounds_.upper_bound(element), bounds_.cbegin() + n_lower_bounds_}};
      return std::nullopt;
    default:
      DLINEAR_UNREACHABLE();
  }
}

bool TheorySolverBoundVector::ViolatedStrictBounds() const {
  if (active_upper_bound_ != active_lower_bound_) return false;
  // The active bounds are equal, verify whether they are violated
  auto nq_value_it = nq_values_.find(active_upper_bound_);
  // No violation, return
  if (nq_value_it == nq_values_.end()) return false;
  // Violated strict bound, remove the last added bound and return the interval
  return true;
}

void TheorySolverBoundVector::Clear() {
  bounds_.clear();
  n_lower_bounds_ = 0;
  nq_values_.clear();
  active_lower_bound_ = inf_l_;
  active_upper_bound_ = inf_u_;
}
void TheorySolverBoundVector::Clear(mpq_class inf) {
  inf_l_ = -inf;
  inf_u_ = std::move(inf);
  Clear();
}
void TheorySolverBoundVector::Clear(mpq_class inf_l, mpq_class inf_u) {
  inf_l_ = std::move(inf_l);
  inf_u_ = std::move(inf_u);
  Clear();
}

bool TheorySolverBoundVector::IsActiveEquality(const mpq_class& value) const {
  if (n_lower_bounds_ == 0 || n_lower_bounds_ == static_cast<int>(bounds_.size())) return false;
  return active_upper_bound_ == active_lower_bound_ && active_upper_bound_ == value;
}

bool TheorySolverBoundVector::IsLowerBound(const mpq_class& value) const {
  if (!bounds_.contains({value, default_lit_})) return false;
  std::cout << "IsLowerBound = distance: "
            << std::distance(bounds_.cbegin(), bounds_.lower_bound({value, default_lit_})) << std::endl;
  return std::distance(bounds_.cbegin(), bounds_.lower_bound({value, default_lit_})) < n_lower_bounds_;
}

bool TheorySolverBoundVector::IsUpperBound(const mpq_class& value) const {
  if (!bounds_.contains({value, default_lit_})) return false;
  std::cout << "IsUpperBound = distance: "
            << std::distance(bounds_.cbegin(), bounds_.upper_bound({value, default_lit_})) << std::endl;
  return std::distance(bounds_.cbegin(), bounds_.upper_bound({value, default_lit_})) > n_lower_bounds_;
}

std::pair<std::optional<TheorySolverBoundVector::Bound>, std::optional<TheorySolverBoundVector::Bound>>
TheorySolverBoundVector::active_bound() const {
  if (bounds_.empty()) return {std::nullopt, std::nullopt};
  if (n_lower_bounds_ == 0) return {std::nullopt, *bounds_.cbegin()};
  if (n_lower_bounds_ == static_cast<int>(bounds_.size())) return {*std::prev(bounds_.cend()), std::nullopt};
  return {bounds_[n_lower_bounds_ - 1], bounds_[n_lower_bounds_]};
}

std::pair<mpq_class, mpq_class> TheorySolverBoundVector::active_bound_value() const {
  return {active_lower_bound_, active_upper_bound_};
}

void TheorySolverBoundVector::SetUpperBound(const mpq_class& value) {
  if (value < active_lower_bound_)
    DLINEAR_RUNTIME_ERROR_FMT("Upper bound must be greater or equal to lower bound. Lower: {}, Upper: {}",
                              active_lower_bound_, active_upper_bound_);
  if (value < active_upper_bound_) active_upper_bound_ = value;
}

void TheorySolverBoundVector::SetLowerBound(const mpq_class& value) {
  if (value > active_upper_bound_)
    DLINEAR_RUNTIME_ERROR_FMT("Upper bound must be greater or equal to lower bound. Lower: {}, Upper: {}",
                              active_lower_bound_, active_upper_bound_);
  if (value > active_lower_bound_) active_lower_bound_ = value;
}
void TheorySolverBoundVector::SetBounds(const mpq_class& lb, const mpq_class& ub) {
  if (std::min(ub, active_upper_bound_) < std::max(lb, active_lower_bound_))
    DLINEAR_RUNTIME_ERROR_FMT("Upper bound must be greater or equal to lower bound. Lower: {}, Upper: {}",
                              active_lower_bound_, active_upper_bound_);
  if (lb > active_lower_bound_) active_lower_bound_ = lb;
  if (ub < active_upper_bound_) active_upper_bound_ = ub;
}

std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector& bounds_vector) {
  os << "TheorySolverBoundVector{ ";
  for (const auto& [value, row_idx] : bounds_vector.bounds()) {
    os << "row " << row_idx << ": " << value << ", ";
  }
  os << "}";
  return os;
}
std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector::Bound& bound) {
  return os << "Bound{ " << bound.first << ", " << bound.second << " }";
}
std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector::Violation& violation) {
  return os << "Violation{ " << *violation.first << ", violation.end() }";
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
