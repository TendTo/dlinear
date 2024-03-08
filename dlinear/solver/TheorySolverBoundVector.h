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

#include <map>
#include <optional>
#include <set>
#include <utility>

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/LpColBound.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/SortedVector.hpp"
#include "dlinear/util/exception.h"

namespace dlinear {

namespace {
using Bound_ = std::tuple<mpq_class, LpColBound, int>;
}

struct BoundComparator {
  bool operator()(const Bound_& lhs, const Bound_& rhs) const;
};

/**
 * TheorySolverBoundVector class.
 *
 * It keeps track of the bounds in the LP solver in a sorted vector.
 * Every time a new bound is added, it checks if it violates any of the existing bounds.
 * This allows to keep track of the active lower and upper bound for the column.
 * If a violation is detected, it returns the iterator to the first and last violated bound.
 * The violating bound is @e not added and the vector remains unchanged.
 */
class TheorySolverBoundVector {
 public:
  using Bound = Bound_;
  using Violation = std::pair<SortedVector<Bound>::const_iterator, SortedVector<Bound>::const_iterator>;

  explicit TheorySolverBoundVector(mpq_class inf);
  TheorySolverBoundVector(mpq_class inf_l, mpq_class inf_u);

  std::optional<Violation> AddBound(const mpq_class& value, LpColBound lp_bound, int lit);
  void SetLowerBound(const mpq_class& value);
  void SetUpperBound(const mpq_class& value);
  void SetBounds(const mpq_class& lb, const mpq_class& ub);

  void Clear();
  void Clear(mpq_class inf);
  void Clear(mpq_class inf_l, mpq_class inf_u);

  [[nodiscard]] int n_upper_bounds() const { return static_cast<int>(bounds_.size()) - n_lower_bounds_; }
  [[nodiscard]] int n_lower_bounds() const { return n_lower_bounds_; }
  [[nodiscard]] Violation active_bounds() const;
  [[nodiscard]] std::pair<mpq_class, mpq_class> active_bound_value() const;
  [[nodiscard]] const SortedVector<Bound, BoundComparator>& bounds() const { return bounds_; }
  [[nodiscard]] const mpq_class& inf_l() const { return inf_l_; }
  [[nodiscard]] const mpq_class& inf_u() const { return inf_u_; }
  [[nodiscard]] const mpq_class& active_lower_bound() const { return active_lower_bound_; }
  [[nodiscard]] const mpq_class& active_upper_bound() const { return active_upper_bound_; }
  [[nodiscard]] const std::set<mpq_class>& nq_values() const { return nq_values_; }

  [[nodiscard]] const Bound& operator[](size_t idx) const { return bounds_[idx]; }

  [[nodiscard]] std::optional<Violation> ViolatedBounds(const mpq_class& value, LpColBound lp_bound) const;
  [[nodiscard]] Violation ViolatedBounds(const mpq_class& value) const;
  [[nodiscard]] bool ViolatedNqBounds() const;
  [[nodiscard]] bool ViolatedNqBounds(const mpq_class& lb, const mpq_class& ub) const;

  [[nodiscard]] bool IsActiveEquality(const mpq_class& value) const;
  [[nodiscard]] bool IsLowerBound(const mpq_class& value) const;
  [[nodiscard]] bool IsUpperBound(const mpq_class& value) const;

 private:
  inline static Bound GetDefaultLowerBound(const mpq_class& value) { return std::make_tuple(value, LpColBound::L, 0); }
  inline static Bound GetDefaultUpperBound(const mpq_class& value) { return std::make_tuple(value, LpColBound::U, 0); }

  [[nodiscard]] inline SortedVector<Bound, BoundComparator>::const_iterator FindLowerBoundValue(
      const mpq_class& value) const {
    return bounds_.lower_bound(GetDefaultLowerBound(value));
  }
  [[nodiscard]] inline SortedVector<Bound, BoundComparator>::const_iterator FindUpperBoundValue(
      const mpq_class& value) const {
    return bounds_.upper_bound(GetDefaultUpperBound(value));
  }

  int n_lower_bounds_;
  SortedVector<Bound, BoundComparator> bounds_;
  std::set<mpq_class> nq_values_;
  mpq_class active_lower_bound_;
  mpq_class active_upper_bound_;
  mpq_class inf_l_;
  mpq_class inf_u_;
};

using TheorySolverBoundVectorMap = std::map<Variable::Id, TheorySolverBoundVector>;
using TheorySolverBoundVectorVector = std::vector<TheorySolverBoundVector>;

std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector& bounds_vector);
std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector::Violation& violation);
std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector::Bound& bound);
std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVectorMap& bounds_vector_map);
std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVectorVector& bounds_vector_vector);

}  // namespace dlinear
