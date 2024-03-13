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
#include <set>
#include <tuple>
#include <utility>
#include <vector>

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/LpColBound.h"
#include "dlinear/solver/TheorySolverBoundIterator.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/SortedVector.hpp"
#include "dlinear/util/exception.h"

namespace dlinear {

struct BoundComparator {
  bool operator()(const std::tuple<mpq_class, LpColBound, int>& lhs,
                  const std::tuple<mpq_class, LpColBound, int>& rhs) const;
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
  using Bound = std::tuple<mpq_class, LpColBound, int>;
  using BoundVector = SortedVector<Bound, BoundComparator>;
  using Violation = TheorySolverBoundIterator<BoundVector>;

  explicit TheorySolverBoundVector(mpq_class inf);
  TheorySolverBoundVector(mpq_class inf_l, mpq_class inf_u);

  Violation AddBound(const mpq_class& value, LpColBound lp_bound, int lit);
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
  [[nodiscard]] const BoundVector& bounds() const { return bounds_; }
  [[nodiscard]] const BoundVector& nq_bounds() const { return nq_bounds_; }
  [[nodiscard]] const mpq_class& inf_l() const { return inf_l_; }
  [[nodiscard]] const mpq_class& inf_u() const { return inf_u_; }
  [[nodiscard]] const mpq_class& active_lower_bound() const { return active_lower_bound_; }
  [[nodiscard]] const mpq_class& active_upper_bound() const { return active_upper_bound_; }

  [[nodiscard]] const Bound& operator[](size_t idx) const { return bounds_[idx]; }

  [[nodiscard]] Violation ViolatedBounds(const mpq_class& value, LpColBound lp_bound) const;
  [[nodiscard]] bool ViolatedNqBounds() const;
  [[nodiscard]] bool ViolatedNqBounds(const mpq_class& lb, const mpq_class& ub) const;

  [[nodiscard]] bool IsActiveEquality(const mpq_class& value) const;
  [[nodiscard]] bool IsLowerBound(const mpq_class& value) const;
  [[nodiscard]] bool IsUpperBound(const mpq_class& value) const;

 private:
  [[nodiscard]] inline BoundVector::const_iterator LowerBoundEnd() const { return bounds_.cbegin() + n_lower_bounds_; }

  [[nodiscard]] inline BoundVector::const_iterator FindLowerBoundValue(const mpq_class& value) const {
    return bounds_.lower_bound({value, LpColBound::L, 0});
  }
  [[nodiscard]] inline BoundVector::const_iterator FindStrictLowerBoundValue(const mpq_class& value) const {
    return bounds_.lower_bound({value, LpColBound::SL, 0});
  }
  [[nodiscard]] inline BoundVector::const_iterator FindLowerBound(const mpq_class& value, LpColBound bound) const {
    return bounds_.lower_bound({value, bound, 0});
  }
  [[nodiscard]] inline BoundVector::const_iterator FindUpperBoundValue(const mpq_class& value) const {
    return bounds_.upper_bound({value, LpColBound::U, 0});
  }
  [[nodiscard]] inline BoundVector::const_iterator FindStrictUpperBoundValue(const mpq_class& value) const {
    return bounds_.upper_bound({value, LpColBound::SU, 0});
  }
  [[nodiscard]] inline BoundVector::const_iterator FindUpperBound(const mpq_class& value, LpColBound bound) const {
    return bounds_.upper_bound({value, bound, 0});
  }
  [[nodiscard]] inline BoundVector::const_iterator FindLowerNqBoundValue(const mpq_class& value) const {
    return nq_bounds_.lower_bound({value, LpColBound::D, 0});
  }
  [[nodiscard]] inline BoundVector::const_iterator FindUpperNqBoundValue(const mpq_class& value) const {
    return nq_bounds_.upper_bound({value, LpColBound::D, 0});
  }

  int n_lower_bounds_;
  BoundVector bounds_;
  BoundVector nq_bounds_;
  mpq_class active_lower_bound_;
  mpq_class active_upper_bound_;
  mpq_class inf_l_;
  mpq_class inf_u_;
};

using TheorySolverBoundVectorMap = std::map<Variable::Id, TheorySolverBoundVector>;
using TheorySolverBoundVectorVector = std::vector<TheorySolverBoundVector>;

std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector& bounds_vector);
std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector::Bound& bound);
std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVectorMap& bounds_vector_map);
std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVectorVector& bounds_vector_vector);

}  // namespace dlinear
