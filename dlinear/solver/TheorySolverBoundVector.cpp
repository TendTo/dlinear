/**
 * @file TheorySolverBoundVector.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "TheorySolverBoundVector.h"

namespace std {

bool less<std::pair<mpq_class, int>>::operator()(const std::pair<mpq_class, int>& lhs,
                                                 const std::pair<mpq_class, int>& rhs) const {
  return lhs.first < rhs.first;
}
}  // namespace std

namespace dlinear {

std::optional<TheorySolverBoundVector::Violation> TheorySolverBoundVector::AddBound(const mpq_class& value,
                                                                                    LpColBound bound, int row_idx) {
  DLINEAR_ASSERT_FMT(bound == LpColBound::L || bound == LpColBound::U || bound == LpColBound::B,
                     "Valid must be L, U or B. Received: {}", bound);
  std::optional<Violation> violation{ViolatedBounds(value, bound)};
  if (violation.has_value()) return violation;

  switch (bound) {
    case LpColBound::L:
      ++n_lower_bounds_;
      break;
    case LpColBound::U:
      break;
    case LpColBound::B:
      bounds_.emplace(value, row_idx);
      ++n_lower_bounds_;
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
  bounds_.emplace(value, row_idx);
  return std::nullopt;
}

std::optional<TheorySolverBoundVector::Violation> TheorySolverBoundVector::ViolatedBounds(const mpq_class& value,
                                                                                          LpColBound bound) const {
  DLINEAR_ASSERT_FMT(bound == LpColBound::L || bound == LpColBound::U || bound == LpColBound::B,
                     "Valid must be L, U or B. Received: {}", bound);

  const Bound element{value, 0};
  long insert_position = 0;
  switch (bound) {
    case LpColBound::L:
      insert_position = std::distance(bounds_.cbegin(), bounds_.lower_bound(element));
      DLINEAR_TRACE_FMT("ViolatedBounds: insert_position = {} | ({} {})", insert_position, value, bound);
      if (insert_position <= n_lower_bounds_) return std::nullopt;
      DLINEAR_ASSERT(bounds_.cbegin() + n_lower_bounds_ < bounds_.lower_bound(element), "Bounds must not be inverted");
      return {{bounds_.cbegin() + n_lower_bounds_, bounds_.lower_bound(element)}};
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

void TheorySolverBoundVector::Clear() {
  bounds_.clear();
  n_lower_bounds_ = 0;
}

bool TheorySolverBoundVector::IsLowerBound(const mpq_class& value) const {
  if (!bounds_.contains({value, 0})) return false;
  std::cout << "IsLowerBound = distance: " << std::distance(bounds_.cbegin(), bounds_.lower_bound({value, 0}))
            << std::endl;
  return std::distance(bounds_.cbegin(), bounds_.lower_bound({value, 0})) < n_lower_bounds_;
}

bool TheorySolverBoundVector::IsUpperBound(const mpq_class& value) const {
  if (!bounds_.contains({value, 0})) return false;
  std::cout << "IsUpperBound = distance: " << std::distance(bounds_.cbegin(), bounds_.upper_bound({value, 0}))
            << std::endl;
  return std::distance(bounds_.cbegin(), bounds_.upper_bound({value, 0})) > n_lower_bounds_;
}

std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector& bounds_vector) {
  os << "TheorySolverBoundVector{ ";
  for (const auto& [value, row_idx] : bounds_vector.bounds()) {
    os << "row " << row_idx << ": " << value << ", ";
  }
  os << "}";
  return os;
}

}  // namespace dlinear
