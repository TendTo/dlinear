#pragma once

#include <algorithm>
#include <iterator>

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
  [[nodiscard]] size_t bounds_size() const { return std::distance(bounds_it_, end_bounds_it_); }
  [[nodiscard]] size_t nq_bounds_size() const { return std::distance(nq_bounds_it_, end_nq_bounds_it_); }
  [[nodiscard]] bool bounds_empty() const { return bounds_it_ == end_bounds_it_; }
  [[nodiscard]] bool nq_bounds_empty() const { return nq_bounds_it_ == end_nq_bounds_it_; }
  [[nodiscard]] bool empty() const { return bounds_empty() && nq_bounds_empty(); }
  [[nodiscard]] size_t size() const { return bounds_size() + nq_bounds_size(); }

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
