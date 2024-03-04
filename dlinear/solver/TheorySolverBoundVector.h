/**
 * @file TheorySolverBoundVector.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Bounds vector used by the theory solver.
 *
 * It keeps track of the bounds in the LP solver in a sorted vector.
 */
#pragma once

#include <utility>

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/LpColBound.h"
#include "dlinear/util/SortedVector.hpp"
#include "dlinear/util/exception.h"

namespace dlinear {

class TheorySolverBoundVector {
  using sorted_value = std::pair<mpq_class, int>;

 public:
  TheorySolverBoundVector() : n_lower_bounds_{0}, bounds_{} {}

  void AddBound(int row_idx, LpColBound bound, const mpq_class& value);
  void Clear();
  [[nodiscard]] bool IsLowerBound(const mpq_class& value) const;
  [[nodiscard]] bool IsUpperBound(const mpq_class& value) const;

  [[nodiscard]] int n_less_than() const { return static_cast<int>(bounds_.size()) - n_lower_bounds_; }
  [[nodiscard]] int n_greater_than() const { return n_lower_bounds_; }
  [[nodiscard]] const SortedVector<sorted_value>& bounds() const { return bounds_; }

  std::pair<mpq_class, int> operator[](size_t idx) const { return bounds_[idx]; }

  [[nodiscard]] std::pair<SortedVector<sorted_value>::const_iterator, SortedVector<sorted_value>::const_iterator>
  ViolatedBounds(const mpq_class& value) const;

 private:
  int n_lower_bounds_;
  SortedVector<sorted_value> bounds_;
};

std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector& bounds_vector);

// Sort the pairs std::pair<mpq_class, null*> by the first element.
bool operator<(const std::pair<mpq_class, int>& lhs, const std::pair<mpq_class, int>& rhs) {
  return lhs.first < rhs.first;
}

}  // namespace dlinear
