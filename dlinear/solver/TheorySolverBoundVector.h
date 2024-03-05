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

#include <optional>
#include <utility>

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/LpColBound.h"
#include "dlinear/util/SortedVector.hpp"
#include "dlinear/util/exception.h"

namespace std {

template <>
struct less<std::pair<mpq_class, int>> {
  bool operator()(const std::pair<mpq_class, int>& lhs, const std::pair<mpq_class, int>& rhs) const;
};

}  // namespace std

namespace dlinear {

class TheorySolverBoundVector {
 public:
  using Bound = std::pair<mpq_class, int>;
  using Violation = std::pair<SortedVector<Bound>::const_iterator, SortedVector<Bound>::const_iterator>;
  TheorySolverBoundVector() : n_lower_bounds_{0}, bounds_{} {}

  std::optional<Violation> AddBound(const mpq_class& value, LpColBound bound, int row_idx);
  void Clear();

  [[nodiscard]] int n_upper_bounds() const { return static_cast<int>(bounds_.size()) - n_lower_bounds_; }
  [[nodiscard]] int n_lower_bounds() const { return n_lower_bounds_; }
  [[nodiscard]] const SortedVector<Bound>& bounds() const { return bounds_; }

  const Bound& operator[](size_t idx) const { return bounds_[idx]; }

  [[nodiscard]] std::optional<Violation> ViolatedBounds(const mpq_class& value, LpColBound bound) const;

  [[nodiscard]] bool IsLowerBound(const mpq_class& value) const;
  [[nodiscard]] bool IsUpperBound(const mpq_class& value) const;

 private:
  int n_lower_bounds_;
  SortedVector<Bound> bounds_;
};

std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector& bounds_vector);

}  // namespace dlinear
