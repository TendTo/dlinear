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

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/LpColBound.h"
#include "dlinear/solver/TheorySolverBoundIterator.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/SortedVector.hpp"
#include "dlinear/util/logging.h"

namespace dlinear {

/**
 * TheorySolverBoundVector class.
 *
 * It keeps track of the bounds in the LP solver in a sorted vector
 * to determine the active lower and upper bound for the column.
 * Every time a new bound is added, it checks if it violates any of the existing bounds.
 * If a violation is detected, it returns the iterator to the first and last violated bound.
 * The violating bound is not added and the vector remains unchanged.
 * @code
 * TheorySolverBoundVector bounds(100);
 * bounds.AddBound(1, LpColBound::L, 1)); // 1 <= x
 * bounds.AddBound(1, LpColBound::SL, 2)); // 1 < x
 * bounds.AddBound(1, LpColBound::L, 4)); // 1 <= x
 * bounds.AddBound(1, LpColBound::SL, 5)); // 1 < x
 * bounds.AddBound(2, LpColBound::SL, 6)); // 2 < x
 * bounds.AddBound(2, LpColBound::L, 7)); // 2 <= x
 * // No violations so far.
 * auto violation = bounds.AddBound(1, LpColBound::U, 10); // x <= 1
 * for (; violation; ++violation) {
 *  std::cout << *violation << std::endl;
 * }
 * // Output:
 * // (1, SL, 2), (1, SL, 5), (2, L, 7), (2, SL, 6)
 * @endcode
 */
class TheorySolverBoundVector {
 public:
  /** Bound. It is a tuple of value, bound type and index */
  struct Bound {
    const mpq_class* value;  ///< Value of the bound
    LpColBound lp_bound;     ///< Type of the bound (e.g. L, SL, U, SU)
    int idx;                 ///< Index of the bound. Refers to the literal associated with the bound

    std::strong_ordering operator<=>(const Bound& other) const;
    bool operator==(const Bound& other) const;
  };
  using BoundVector = SortedVector<Bound>;                       ///< Sorted vector of bounds
  using BoundIterator = TheorySolverBoundIterator<BoundVector>;  ///< BoundIterator iterator over the violated bounds

  /**
   * Construct a new TheorySolverBoundVector using @p inf_l as the the lower bound and @p inf_u as the upper bound.
   * @param inf_l lower bound
   * @param inf_u upper bound
   */
  TheorySolverBoundVector(const mpq_class& inf_l, const mpq_class& inf_u);

  /**
   * Add a new bound to the vector.
   *
   * The bound will be sorted in the vector according to its value and type with the goal of identifying
   * violating bounds as fast a possible.
   * @note If a violation is detected, the bound will not be added. The vector will remain unchanged.
   * @param bound bound to add
   * @return empty @ref BoundIterator if the bound has been added successfully, otherwise a @ref BoundIterator
   * containing
   * @return @ref BoundIterator containing all the violated bounds in the vector
   * @see AddBound(const mpq_class&, LpColBound, int)
   */
  BoundIterator AddBound(const Bound& bound);
  /**
   * Add a new bound to the vector.
   *
   * The bound will be sorted in the vector according to its value and type with the goal of identifying
   * violating bounds as fast a possible.
   * The @p idx it is ignored by the @ref TheorySolverBoundVector, but can be used by the caller to identify the bound.
   * Before adding a new bound, a check is performed to ensure it does not violate any of the existing bounds.
   * If a violation is detected, a @ref BoundIterator containing all the violated bounds is returned instead.
   * @note If a violation is detected, the bound will not be added. The vector will remain unchanged.
   * @param value value of the new bound
   * @param lp_bound type of the new bound
   * @param idx literal associated with the bound
   * @return empty @ref BoundIterator if the bound has been added successfully, otherwise a @ref BoundIterator
   * containing
   * @return @ref BoundIterator containing all the violated bounds in the vector
   */
  BoundIterator AddBound(const mpq_class& value, LpColBound lp_bound, int idx);
  /**
   * Manually set the active lower bound to @p value.
   *
   * The method won't have any effect if @p value is less than the active lower bound.
   * @param value value of the new lower bound
   * @throw std::runtime_error if the value is greater than the active upper bound
   */
  void SetLowerBound(const mpq_class& value);
  /**
   * Manually set the active upper bound to @p value.
   *
   * The method won't have any effect if @p value is greater than the active upper bound.
   * @param value value of the new upper bound
   * @throw std::runtime_error if the value is less than the active lower bound
   */
  void SetUpperBound(const mpq_class& value);
  /**
   * Manually set the active bounds to @p lb and @p ub.
   *
   * The active bounds will be set to @p lb and @p ub only if @p lb is greater than the active lower bound
   * and @p ub is less than the active upper bound respectively.
   * @param lb new lower bound
   * @param ub new upper bound
   * @throw std::runtime_error if after setting the bounds, the lower bound is greater than the upper bound
   */
  void SetBounds(const mpq_class& lb, const mpq_class& ub);

  /**
   * Clear the vector and reset the active bounds.
   *
   * Active bounds are set to @ref inf_l_ and @ref inf_u_.
   */
  void Clear();

  /**
   * Return the number of lower bounds in the vector, both strict and non-strict.
   * @return number of lower bounds
   */
  [[nodiscard]] int n_lower_bounds() const { return n_lower_bounds_; }
  /**
   * Return the number of upper bounds in the vector, both strict and non-strict.
   * @return number of upper bounds
   */
  [[nodiscard]] int n_upper_bounds() const { return static_cast<int>(bounds_.size()) - n_lower_bounds_; }
  /**
   * Return a @ref BoundIterator containing a minimal set of bounds
   * enclosing the interval [@ref active_lower_bound_, @ref active_upper_bound_]
   * as well as all the not-equal constraints in that interval.
   * @return iterator over the active bounds
   * @see GetActiveBounds
   */
  [[nodiscard]] BoundIterator GetActiveBound() const;
  /**
   * Return a @ref BoundIterator containing a minimal set of bounds enclosing the interval [@p value, @p value]
   * as well as all the not-equal constraints in that interval.
   * @param value value to check
   * @return iterator over the active bounds
   * @see GetActiveBounds
   */
  [[nodiscard]] BoundIterator GetActiveBound(const mpq_class& value) const;
  /**
   * Return a @ref BoundIterator containing a set of bounds
   * enclosing the interval [@ref active_lower_bound_, @ref active_upper_bound_]
   * as well as all the not-equal constraints in that interval.
   * @note Equality bounds will hide not matching inequality bounds.
   * @return iterator over the active bounds
   * @see GetActiveBound
   */
  [[nodiscard]] BoundIterator GetActiveBounds() const;
  /**
   * Return a @ref BoundIterator containing a set of bounds enclosing the interval [@p value, @p value]
   * as well as all the not-equal constraints in that interval.
   * @param value value to check
   * @note Equality bounds will hide not matching inequality bounds.
   * @return iterator over the active bounds
   * @see GetActiveBound
   */
  [[nodiscard]] BoundIterator GetActiveBounds(const mpq_class& value) const;
  /**
   * Produce a @ref LiteralSet containing all the active bounds that can be used as an explanation.
   *
   * It uses @p theory_bound_to_lit to match the active bounds to the corresponding literal.
   * @param theory_bound_to_lit map between the bound id and the theory literal
   * @param explanation set of literal corresponding to the explanation
   */
  void GetActiveExplanation(const std::vector<Literal>& theory_bound_to_lit, LiteralSet& explanation) const;
  /**
   * Produce a @ref LiteralSet containing all the active bounds that can be used as an explanation.
   *
   * It uses @p theory_bound_to_lit to match the active bounds to the corresponding literal.
   * @param theory_bound_to_lit map between the bound id and the theory literal
   * @return set of literal corresponding to the explanation
   */
  [[nodiscard]] LiteralSet GetActiveExplanation(const std::vector<Literal>& theory_bound_to_lit) const;
  /**
   * Produce a @ref LiteralSet containing all the active bounds that can be used as an explanation, only if the
   * variable presents an equality active bound.
   *
   * It uses @p theory_bound_to_lit to match the active bounds to the corresponding literal.
   * @param theory_bound_to_lit map between the bound id and the theory literal
   * @param explanation set of literal corresponding to the explanation
   * @see GetActiveExplanation
   */
  void GetActiveEqExplanation(const std::vector<Literal>& theory_bound_to_lit, LiteralSet& explanation) const;
  /**
   * Produce a @ref LiteralSet containing all the active bounds that can be used as an explanation, only if the
   * variable presents an equality active bound.
   *
   * It uses @p theory_bound_to_lit to match the active bounds to the corresponding literal.
   * @param theory_bound_to_lit map between the bound id and the theory literal
   * @return set of literal corresponding to the explanation
   * @see GetActiveExplanation
   */
  [[nodiscard]] LiteralSet GetActiveEqExplanation(const std::vector<Literal>& theory_bound_to_lit) const;
  /**
   * Return a pair containing the active lower and upper bound.
   * @return active lower and upper bound
   */
  [[nodiscard]] std::pair<const mpq_class&, const mpq_class&> GetActiveBoundsValue() const;
  /**
   * Return the bounds vector.
   *
   * It contains all the bounds, both equality and inequality, except for the non-equality bounds.
   * @return bounds vector
   */
  [[nodiscard]] const BoundVector& bounds() const { return bounds_; }
  /**
   * Return the non-equality bounds vector.
   *
   * It only contains the non-equality bounds.
   * @return non-equality bounds vector
   */
  [[nodiscard]] const BoundVector& nq_bounds() const { return nq_bounds_; }
  /**
   * Return the starting lower bound.
   * @return starting lower bound
   */
  [[nodiscard]] const mpq_class& inf_l() const { return *inf_l_; }
  /**
   * Return the starting upper bound.
   * @return starting upper bound
   */
  [[nodiscard]] const mpq_class& inf_u() const { return *inf_u_; }
  /**
   * Return the active lower bound.
   * @return active lower bound
   */
  [[nodiscard]] const mpq_class& active_lower_bound() const { return *active_lower_bound_; }
  /**
   * Return the active upper bound.
   * @return active upper bound
   */
  [[nodiscard]] const mpq_class& active_upper_bound() const { return *active_upper_bound_; }

  /**
   * Return the active equality bound.
   *
   * An active equality bound is obtained when the active lower bound is equal to the active upper bound.
   * If such condition is false, a nullptr is returned.
   * @return active equality bound if the active lower bound is equal to the active upper bound
   * @return nullptr if the active lower bound is not equal to the active upper bound
   */
  [[nodiscard]] const mpq_class* GetActiveEqualityBound() const {
    return IsActiveEquality(*active_lower_bound_) ? active_lower_bound_ : nullptr;
  }

  [[nodiscard]] const Bound& operator[](size_t idx) const { return bounds_[idx]; }

  /**
   * Check if the combination of @p value and @p lp_bound violates any of the existing bounds.
   *
   * If that is the case, a non-empty @ref BoundIterator containing all the violated bounds is returned.
   * @param value value of the bound
   * @param lp_bound type of the bound
   * @return empty @ref BoundIterator if the bound does not violate any of the existing bounds
   * @return @ref BoundIterator containing all the violated existing bounds
   */
  [[nodiscard]] BoundIterator ViolatedBounds(const mpq_class& value, LpColBound lp_bound) const;
  /**
   * Check if the active bounds violate any of the existing non-equality bounds.
   * @return true if the active bounds violate any of the existing non-equality bounds
   * @return false if no violation is detected
   */
  [[nodiscard]] bool ViolatedNqBounds() const;
  /**
   * Check if the new combination of @p lb and @p ub violates any of the existing non-equality bounds.
   * @param lb lower bound
   * @param ub upper bound
   * @return true if the new combination of @p lb and @p ub violates any of the existing non-equality bounds
   * @return false if no violation is detected
   */
  [[nodiscard]] bool ViolatedNqBounds(const mpq_class& lb, const mpq_class& ub) const;

  /**
   * Check if @p value represents an equality bound.
   * @param value value to check
   * @return true if @p value represents an equality bound
   * @return false if @p value does not represent an equality bound
   */
  [[nodiscard]] bool IsActiveEquality(const mpq_class& value) const;
  /**
   * Check if @p value represents a lower bound.
   * @param value value to check
   * @return true if @p value represents a lower bound
   * @return false if @p value does not represent a lower bound
   */
  [[nodiscard]] bool IsLowerBound(const mpq_class& value) const;

  /**
   * Check if @p value represents an upper bound.
   * @param value value to check
   * @return true if @p value represents an upper bound
   * @return false if @p value does not represent an upper bound
   */
  [[nodiscard]] bool IsUpperBound(const mpq_class& value) const;

 private:
  /**
   * Return an iterator over @ref bounds_ after the last lower bound and to the first upper bound.
   * @return iterator after the last lower bound and to the first upper bound
   */
  [[nodiscard]] inline BoundVector::const_iterator LowerBoundEnd() const { return bounds_.cbegin() + n_lower_bounds_; }
  /**
   * Return a @ref BoundIterator containing a minimal set of bounds enclosing the interval [@p lb, @p ub]
   * as well as all the not-equal constraints in that interval.
   * @pre @code (lb == active_lower_bound_ && ub == active_upper_bound_) || lb == ub @endcode
   * @pre @code lb <= ub @endcode
   * @param lb lower bound
   * @param ub upper bound
   * @return iterator over the active bounds
   */
  [[nodiscard]] BoundIterator GetActiveBound(const mpq_class& lb, const mpq_class& ub) const;
  /**
   * Return a @ref BoundIterator containing the set of bounds enclosing the interval [@p lb, @p ub]
   * as well as all the not-equal constraints in that interval.
   * @note Equality bounds will hide not matching inequality bounds.
   * @pre @code (lb == active_lower_bound_ && ub == active_upper_bound_) || lb == ub @endcode
   * @pre @code lb <= ub @endcode
   * @param lb lower bound
   * @param ub upper bound
   * @return iterator over the active bounds
   */
  [[nodiscard]] BoundIterator GetActiveBounds(const mpq_class& lb, const mpq_class& ub) const;

  int n_lower_bounds_;                   ///< Number of lower bounds, both strict and non-strict
  BoundVector bounds_;                   ///< Equality and inequality bounds
  BoundVector nq_bounds_;                ///< Non-equality bounds
  const mpq_class* const inf_l_;         ///< Starting lower bound
  const mpq_class* const inf_u_;         ///< Starting upper bound
  const mpq_class* active_lower_bound_;  ///< Active lower bound
  const mpq_class* active_upper_bound_;  ///< Active upper bound
};

using TheorySolverBoundVectorMap = std::map<Variable::Id, TheorySolverBoundVector>;
using TheorySolverBoundVectorVector = std::vector<TheorySolverBoundVector>;

std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector& bounds_vector);
std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVector::Bound& bound);
std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVectorMap& bounds_vector_map);
std::ostream& operator<<(std::ostream& os, const TheorySolverBoundVectorVector& bounds_vector_vector);

}  // namespace dlinear

OSTREAM_FORMATTER(dlinear::TheorySolverBoundVector::Bound)
OSTREAM_FORMATTER(dlinear::TheorySolverBoundVector::BoundIterator)
OSTREAM_FORMATTER(dlinear::TheorySolverBoundVector)
OSTREAM_FORMATTER(dlinear::TheorySolverBoundVectorMap)
OSTREAM_FORMATTER(dlinear::TheorySolverBoundVectorVector)
