/**
 * @file TheorySolverBoundIterator.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief TheorySolverBoundIterator class.
 *
 * It is used to iterate over the bounds of a theory solver without copying the @ref Bounds.
 * Usually the results of bound violation.
 */
#pragma once

#include <algorithm>
#include <iterator>
#include <utility>

namespace dlinear {

template <class T>
class TheorySolverBoundIterator {
 public:
  using vector_type = T;
  using internal_iterator = typename vector_type::const_iterator;
  using iterator_category = std::input_iterator_tag;
  using value_type = typename vector_type::value_type;
  using reference = value_type const &;
  using pointer = value_type const *;
  using difference_type = ptrdiff_t;

  TheorySolverBoundIterator();
  TheorySolverBoundIterator(internal_iterator begin_bounds_it, internal_iterator end_bounds_it);
  explicit TheorySolverBoundIterator(std::pair<internal_iterator, internal_iterator> bounds);
  TheorySolverBoundIterator(internal_iterator begin_bounds_it, internal_iterator end_bounds_it,
                            internal_iterator begin_nq_bounds_it, internal_iterator end_nq_bounds_it);
  TheorySolverBoundIterator(std::pair<internal_iterator, internal_iterator> bounds,
                            std::pair<internal_iterator, internal_iterator> nq_bounds);

  explicit operator bool() const { return bounds_it_ != end_bounds_it_ || nq_bounds_it_ != end_nq_bounds_it_; }

  pointer operator->() const { return bounds_it_ != end_bounds_it_ ? &*bounds_it_ : &*nq_bounds_it_; }
  reference operator*() const { return bounds_it_ != end_bounds_it_ ? *bounds_it_ : *nq_bounds_it_; }

  TheorySolverBoundIterator &operator++();
  const TheorySolverBoundIterator operator++(int);

  TheorySolverBoundIterator &operator--();
  const TheorySolverBoundIterator operator--(int);

  value_type operator[](int i) const;

  std::pair<internal_iterator, internal_iterator> bounds() const { return {bounds_it_, end_bounds_it_}; }
  std::pair<internal_iterator, internal_iterator> nq_bounds() const { return {nq_bounds_it_, end_nq_bounds_it_}; }
  [[nodiscard]] inline size_t bounds_size() const { return std::distance(bounds_it_, end_bounds_it_); }
  [[nodiscard]] inline size_t nq_bounds_size() const { return std::distance(nq_bounds_it_, end_nq_bounds_it_); }
  [[nodiscard]] inline bool bounds_empty() const { return bounds_it_ == end_bounds_it_; }
  [[nodiscard]] inline bool nq_bounds_empty() const { return nq_bounds_it_ == end_nq_bounds_it_; }
  [[nodiscard]] inline bool empty() const { return bounds_empty() && nq_bounds_empty(); }
  [[nodiscard]] inline size_t size() const { return bounds_size() + nq_bounds_size(); }

 private:
  static const vector_type default_empty_vector_;

  const internal_iterator begin_bounds_it_;
  internal_iterator bounds_it_;
  const internal_iterator end_bounds_it_;

  const internal_iterator begin_nq_bounds_it_;
  internal_iterator nq_bounds_it_;
  const internal_iterator end_nq_bounds_it_;
};

template <class T>
std::ostream &operator<<(std::ostream &os, const TheorySolverBoundIterator<T> &violation);

}  // namespace dlinear
