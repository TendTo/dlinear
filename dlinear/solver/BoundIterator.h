/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * @brief BoundIterator class.
 *
 * It is used to iterate over the bounds of a theory solver without copying each @ref
 * dlinear::BoundVector::Bound. Usually the results of bound violation.
 */
#pragma once

#include <cstddef>
#include <iosfwd>
#include <iterator>
#include <optional>
#include <utility>
#include <vector>

#include "dlinear/solver/Bound.h"

namespace dlinear {

/**
 * BoundIterator class.
 *
 * It is used to iterate over the bounds of a theory solver without copying each @ref BoundVector::Bound.
 * Can be returned as a result of a bound violation or to iterate over the active bounds.
 * It allows to iterate over the two types of bounds: standard and non-equal as if they were a single container.
 * @code
 * std::vector<Bound> bounds, nq_bounds;
 * bounds.push_back(Bound{0, BoundType::U, ...});
 * bounds.push_back(Bound{1, BoundType::L, ...});
 * bounds.push_back(Bound{2, BoundType::B, ...});
 * nq_bounds.push_back(Bound{3, BoundType::D, ...});
 * BoundIterator<std::vector<Bound>> it{bounds.begin(), bounds.end(), nq_bounds.begin(), nq_bounds.end()};
 * for (; it; ++it) {
 *  std::cout << *it << std::endl;
 * }
 * // Output:
 * // Bound{0, BoundType::U, ...}, Bound{1, BoundType::L, ...}, Bound{2, BoundType::B, ...}, Bound{3, BoundType::D, ...}
 * @endcode
 */
class BoundIterator {
 public:
  using vector_type = std::vector<Bound>;
  using internal_iterator = typename vector_type::const_iterator;
  using iterator_category = std::input_iterator_tag;
  using value_type = typename vector_type::value_type;
  using reference = value_type const &;
  using pointer = value_type const *;
  using difference_type = std::ptrdiff_t;

  /** Construct an empty iterator. */
  BoundIterator();
  /**
   * Construct an iterator from a pair of iterators, @p begin_bounds_it and @p end_bounds_it.
   * @note Bounds will be normalized, i.e., all ending bounds will be greater or equal to the being bounds.
   * @param begin_bounds_it begin iterator to the first bound
   * @param end_bounds_it end iterator of the bounds
   */
  BoundIterator(internal_iterator begin_bounds_it, internal_iterator end_bounds_it);
  /**
   * Construct an iterator from a pair of iterators, @p bounds.
   * @note Bounds will be normalized, i.e., all ending bounds will be greater or equal to the being bounds.
   * @param bounds pair of iterators to the bounds, begin and end
   */
  explicit BoundIterator(std::pair<internal_iterator, internal_iterator> bounds);
  /**
   * Construct an iterator from a pair of iterators to the standard bounds, @p begin_bounds_it and @p end_bounds_it,
   * and a pair of iterators to the non-equal bounds, @p begin_nq_bounds_it and @p end_nq_bounds_it.
   * @note Bounds will be normalized, i.e., all ending bounds will be greater or equal to the being bounds.
   * @param begin_bounds_it begin iterator to the first bound
   * @param end_bounds_it end iterator of the bounds
   * @param begin_nq_bounds_it begin iterator to the first non-equal bound
   * @param end_nq_bounds_it end iterator of the non-equal bounds
   */
  BoundIterator(internal_iterator begin_bounds_it, internal_iterator end_bounds_it,
                internal_iterator begin_nq_bounds_it, internal_iterator end_nq_bounds_it);
  /**
   * Construct an iterator from a pair of iterators to the standard bounds, @p bounds,
   * and a pair of iterators to the non-equal bounds, @p nq_bounds.
   * @note Bounds will be normalized, i.e., all ending bounds will be greater or equal to the being bounds.
   * @param bounds begin and end iterators to the bounds
   * @param nq_bounds begin and end iterators to the non-equal bounds
   */
  BoundIterator(std::pair<internal_iterator, internal_iterator> bounds,
                std::pair<internal_iterator, internal_iterator> nq_bounds);

  explicit operator bool() const { return bounds_it_ != end_bounds_it_ || nq_bounds_it_ != end_nq_bounds_it_; }

  pointer operator->() const { return bounds_it_ != end_bounds_it_ ? &*bounds_it_ : &*nq_bounds_it_; }
  reference operator*() const { return bounds_it_ != end_bounds_it_ ? *bounds_it_ : *nq_bounds_it_; }

  BoundIterator &operator++();
  const BoundIterator operator++(int);

  BoundIterator &operator--();
  const BoundIterator operator--(int);

  value_type operator[](int i) const;

  /**
   * Return the pair of iterators to the bounds.
   * @return begin and end iterators to the bounds
   */
  [[nodiscard]] std::pair<internal_iterator, internal_iterator> bounds() const { return {bounds_it_, end_bounds_it_}; }
  /**
   * Return the pair of iterators to the non-equal bounds.
   * @return begin and end iterators to the non-equal bounds
   */
  [[nodiscard]] std::pair<internal_iterator, internal_iterator> nq_bounds() const {
    return {nq_bounds_it_, end_nq_bounds_it_};
  }
  /**
   * Number of bounds included between the begin and end iterators.
   * @return number of bounds
   */
  [[nodiscard]] inline std::size_t bounds_size() const { return std::distance(bounds_it_, end_bounds_it_); }
  /**
   * Number of non-equal bounds included between the begin and end iterators.
   * @return number of non-equal bounds
   */
  [[nodiscard]] inline std::size_t nq_bounds_size() const { return std::distance(nq_bounds_it_, end_nq_bounds_it_); }
  /**
   * Check if the iterator does not point to any bound.
   * @note Equivalent to bounds_size() == 0
   * @return true if the iterator does not point to any bound
   * @return false if the iterator points to at least one bound
   */
  [[nodiscard]] inline bool bounds_empty() const { return bounds_it_ == end_bounds_it_; }
  /**
   * Check if the iterator does not point to any non-equal bound.
   * @note Equivalent to nq_bounds_size() == 0
   * @return true if the iterator does not point to any non-equal bound
   * @return false if the iterator points to at least one non-equal bound
   */
  [[nodiscard]] inline bool nq_bounds_empty() const { return nq_bounds_it_ == end_nq_bounds_it_; }
  /**
   * Check if the iterator does not point to any bound.
   * @note Equivalent to bounds_empty() && nq_bounds_empty()
   * @return true if the iterator does not point to any bound
   * @return false if the iterator points to at least one bound
   */
  [[nodiscard]] inline bool empty() const { return bounds_empty() && nq_bounds_empty(); }
  /**
   * Number of bounds of any kind included between the begin and end iterators.
   * @note Equivalent to bounds_size() + nq_bounds_size()
   * @return number of bounds of any kind
   */
  [[nodiscard]] inline std::size_t size() const { return bounds_size() + nq_bounds_size(); }

  /** @getter{begin iterator, BoundIterator} */
  [[nodiscard]] internal_iterator begin() const { return bounds_it_; }
  /** @getter{end iterator, BoundIterator} */
  [[nodiscard]] internal_iterator end() const { return end_nq_bounds_it_; }

  /**
   * Produce and explanation formed by all the theory literals present in the violation.
   *
   * It puts in a single set all the explanations and literals of all the bounds.
   * @return explanation
   */
  [[nodiscard]] LiteralSet explanation() const;
  /**
   * Produce and explanation formed by all the theory literals present in the violation.
   *
   * It puts in a single set all the explanations and literals of all the bounds.
   * @param explanation[out] set to store the explanation
   * @return explanation
   */
  void explanation(LiteralSet &explanation) const;
  /**
   * Produce a set of explanations.
   *
   * Each of the explanations is produced from a single bound of the violation,
   * putting together its explanation and literal.
   * If @p lit is present, it will be added to every explanation.
   * @param lit if specified, it is added to all explanations
   * @return set of explanations
   */
  [[nodiscard]] std::set<LiteralSet> explanations(const std::optional<Literal> &lit = {}) const;
  /**
   * Produce a set of explanations.
   *
   * Each of the explanations is produced from a single bound of the violation,
   * putting together its explanation and literal.
   * If @p lit is present, it will be added to every explanation.
   * @param explanations[out] set to store the explanations
   * @param lit if specified, it is added to all explanations
   * @return set of explanations
   */
  void explanations(std::set<LiteralSet> &explanations, const std::optional<Literal> &lit = {}) const;

 private:
  static const vector_type default_empty_vector_;  ///< Default empty vector. Used for default construction.

  const internal_iterator begin_bounds_it_;  ///< Begin iterator to the first bound
  internal_iterator bounds_it_;              ///< Iterator to the current bound
  const internal_iterator end_bounds_it_;    ///< End iterator of the bounds

  const internal_iterator begin_nq_bounds_it_;  ///< Begin iterator to the first non-equal bound
  internal_iterator nq_bounds_it_;              ///< Iterator to the current non-equal bound
  const internal_iterator end_nq_bounds_it_;    ///< End iterator of the non-equal bounds
};

std::ostream &operator<<(std::ostream &os, const BoundIterator &violation);

}  // namespace dlinear
