/**
 * @file TheorySolverBoundVector.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "TheorySolverBoundVector.h"

namespace dlinear {

void TheorySolverBoundVector::AddBound(int row_idx, LpColBound bound, const mpq_class& value) {
  DLINEAR_ASSERT_FMT(bound == LpColBound::L || bound == LpColBound::U || bound == LpColBound::B,
                     "Valid must be L, U or B. Received: {}", bound);
  switch (bound) {
    case LpColBound::L:
      bounds_.emplace(value, row_idx);
      break;
    case LpColBound::U:
      bounds_.emplace(value, row_idx);
      ++n_lower_bounds_;
      break;
    case LpColBound::B:
      bounds_.emplace(value, row_idx);
      bounds_.emplace(value, row_idx);
      ++n_lower_bounds_;
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::pair<SortedVector<TheorySolverBoundVector::sorted_value>::const_iterator,
          SortedVector<TheorySolverBoundVector::sorted_value>::const_iterator>
TheorySolverBoundVector::ViolatedBounds(const mpq_class& value) const {
  DLINEAR_ASSERT(!bounds_.empty(), "No bounds in the vector");
  const sorted_value element{value, 0};
  std::pair<SortedVector<sorted_value>::const_iterator, SortedVector<sorted_value>::const_iterator> result{
      bounds_.greater_begin(element), bounds_.lesser_end(element)};
  DLINEAR_ASSERT((IsUpperBound(value) || IsLowerBound(value)), "Value must be either upper or lower bound.");
  if (IsLowerBound(value)) result.first = bounds_.cbegin();
  if (IsUpperBound(value)) result.second = bounds_.cend();
  return result;
}

void TheorySolverBoundVector::Clear() {
  bounds_.clear();
  n_lower_bounds_ = 0;
}

bool TheorySolverBoundVector::IsLowerBound(const mpq_class& value) const {
  return std::distance(bounds_.cbegin(), bounds_.greater_begin({value, 0})) <= n_lower_bounds_;
}

bool TheorySolverBoundVector::IsUpperBound(const mpq_class& value) const {
  return std::distance(bounds_.cbegin(), bounds_.lesser_end({value, 0})) > n_lower_bounds_;
}

std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector& bounds_vector) {
  os << "TheorySolverBoundVector{";
  for (const auto& [var, bounds] : bounds_vector.bounds()) {
    os << var << " -> " << bounds << ", ";
  }
  os << "}";
  return os;
}

}  // namespace dlinear
