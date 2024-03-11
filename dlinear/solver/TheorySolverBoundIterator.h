#pragma once

#include <algorithm>
#include <iterator>

#include "dlinear/util/SortedVector.hpp"

namespace dlinear {

template <class T, class Comparator = std::less<T>>
class TheorySolverBoundIterator {
 public:
  using vector_type = SortedVector<T, Comparator>;
  using internal_iterator = typename vector_type::const_iterator;
  using iterator_category = std::input_iterator_tag;
  using value_type = typename vector_type::value_type;
  using reference = value_type const &;
  using pointer = value_type const *;
  using difference_type = ptrdiff_t;

  explicit TheorySolverBoundIterator(internal_iterator begin_bounds_it, internal_iterator end_bounds_it);
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

  [[nodiscard]] size_t size() const {
    return std::distance(begin_bounds_it_, end_bounds_it_) + std::distance(begin_nq_bounds_it_, end_nq_bounds_it_);
  }

  const internal_iterator begin_bounds_it_;
  internal_iterator bounds_it_;
  const internal_iterator end_bounds_it_;

  const internal_iterator begin_nq_bounds_it_;
  internal_iterator nq_bounds_it_;
  const internal_iterator end_nq_bounds_it_;
};

}  // namespace dlinear
