#include "TheorySolverBoundIterator.h"

#include "dlinear/solver/TheorySolverBoundVector.h"
#include "dlinear/util/SortedVector.hpp"

namespace dlinear {

template <class T>
const typename TheorySolverBoundIterator<T>::vector_type TheorySolverBoundIterator<T>::default_empty_vector_{};

template <class T>
TheorySolverBoundIterator<T>::TheorySolverBoundIterator()
    : begin_bounds_it_(default_empty_vector_.cend()),
      bounds_it_(default_empty_vector_.cend()),
      end_bounds_it_(default_empty_vector_.cend()),
      begin_nq_bounds_it_(default_empty_vector_.cend()),
      nq_bounds_it_(default_empty_vector_.cend()),
      end_nq_bounds_it_(default_empty_vector_.cend()) {}

template <class T>
TheorySolverBoundIterator<T>::TheorySolverBoundIterator(
    TheorySolverBoundIterator<T>::internal_iterator begin_bounds_it,
    TheorySolverBoundIterator<T>::internal_iterator end_bounds_it,
    TheorySolverBoundIterator<T>::internal_iterator begin_nq_bounds_it,
    TheorySolverBoundIterator<T>::internal_iterator end_nq_bounds_it)
    : begin_bounds_it_(begin_bounds_it),
      bounds_it_(begin_bounds_it),
      end_bounds_it_(end_bounds_it),
      begin_nq_bounds_it_(begin_nq_bounds_it),
      nq_bounds_it_(begin_nq_bounds_it),
      end_nq_bounds_it_(end_nq_bounds_it) {}
template <class T>
TheorySolverBoundIterator<T>::TheorySolverBoundIterator(
    std::pair<TheorySolverBoundIterator<T>::internal_iterator, TheorySolverBoundIterator<T>::internal_iterator> bounds,
    std::pair<TheorySolverBoundIterator<T>::internal_iterator, TheorySolverBoundIterator<T>::internal_iterator>
        nq_bounds)
    : begin_bounds_it_(bounds.first),
      bounds_it_(bounds.first),
      end_bounds_it_(bounds.second),
      begin_nq_bounds_it_(nq_bounds.first),
      nq_bounds_it_(nq_bounds.first),
      end_nq_bounds_it_(nq_bounds.second) {}
template <class T>
TheorySolverBoundIterator<T>::TheorySolverBoundIterator(TheorySolverBoundIterator<T>::internal_iterator begin_bounds_it,
                                                        TheorySolverBoundIterator<T>::internal_iterator end_bounds_it)
    : begin_bounds_it_(begin_bounds_it),
      bounds_it_(begin_bounds_it),
      end_bounds_it_(end_bounds_it),
      begin_nq_bounds_it_(default_empty_vector_.cend()),
      nq_bounds_it_(default_empty_vector_.cend()),
      end_nq_bounds_it_(default_empty_vector_.cend()) {}
template <class T>
TheorySolverBoundIterator<T>::TheorySolverBoundIterator(
    std::pair<TheorySolverBoundIterator<T>::internal_iterator, TheorySolverBoundIterator<T>::internal_iterator> bounds)
    : begin_bounds_it_(bounds.first),
      bounds_it_(bounds.first),
      end_bounds_it_(bounds.second),
      begin_nq_bounds_it_(default_empty_vector_.cend()),
      nq_bounds_it_(default_empty_vector_.cend()),
      end_nq_bounds_it_(default_empty_vector_.cend()) {}

template <class T>
TheorySolverBoundIterator<T> &TheorySolverBoundIterator<T>::operator++() {
  if (bounds_it_ != end_bounds_it_) {
    ++bounds_it_;
  } else if (nq_bounds_it_ != end_nq_bounds_it_) {
    ++nq_bounds_it_;
  }
  return *this;
}

template <class T>
const TheorySolverBoundIterator<T> TheorySolverBoundIterator<T>::operator++(int) {
  TheorySolverBoundIterator tmp = *this;
  ++*this;
  return tmp;
}

template <class T>
TheorySolverBoundIterator<T> &TheorySolverBoundIterator<T>::operator--() {
  if (nq_bounds_it_ != begin_nq_bounds_it_) {
    --nq_bounds_it_;
  } else if (bounds_it_ != begin_bounds_it_) {
    --bounds_it_;
  }
  return *this;
}
template <class T>
const TheorySolverBoundIterator<T> TheorySolverBoundIterator<T>::operator--(int) {
  TheorySolverBoundIterator tmp = *this;
  --*this;
  return tmp;
}
template <class T>
typename TheorySolverBoundIterator<T>::value_type TheorySolverBoundIterator<T>::operator[](int i) const {
  const int distance = std::distance(begin_bounds_it_, end_bounds_it_);
  return i < distance ? *(bounds_it_ + i) : *(nq_bounds_it_ + i - distance);
}

template <class T>
std::ostream &operator<<(std::ostream &os, const TheorySolverBoundIterator<T> &violation) {
  TheorySolverBoundIterator<T> it{violation.bounds(), violation.nq_bounds()};
  os << "TheorySolverBoundIterator{";
  for (size_t i = 0; it; ++it, ++i) {
    os << *it;
    if (i + 1 < it.size()) {
      os << ", ";
    }
  }
  return os << "}";
}

template class TheorySolverBoundIterator<SortedVector<TheorySolverBoundVector::Bound, BoundComparator>>;
template std::ostream &operator<<(
    std::ostream &os,
    const TheorySolverBoundIterator<SortedVector<TheorySolverBoundVector::Bound, BoundComparator>> &violation);

}  // namespace dlinear