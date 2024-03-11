#include "TheorySolverBoundIterator.h"

#include "dlinear/solver/TheorySolverBoundVector.h"

namespace dlinear {

template <class T, class Comparator>
TheorySolverBoundIterator<T, Comparator>::TheorySolverBoundIterator(
    TheorySolverBoundIterator<T, Comparator>::internal_iterator begin_bounds_it,
    TheorySolverBoundIterator<T, Comparator>::internal_iterator end_bounds_it,
    TheorySolverBoundIterator<T, Comparator>::internal_iterator begin_nq_bounds_it,
    TheorySolverBoundIterator<T, Comparator>::internal_iterator end_nq_bounds_it)
    : begin_bounds_it_(begin_bounds_it),
      bounds_it_(begin_bounds_it),
      end_bounds_it_(end_bounds_it),
      begin_nq_bounds_it_(begin_nq_bounds_it),
      nq_bounds_it_(begin_nq_bounds_it),
      end_nq_bounds_it_(end_nq_bounds_it) {}
template <class T, class Comparator>
TheorySolverBoundIterator<T, Comparator>::TheorySolverBoundIterator(
    std::pair<TheorySolverBoundIterator<T, Comparator>::internal_iterator,
              TheorySolverBoundIterator<T, Comparator>::internal_iterator>
        bounds,
    std::pair<TheorySolverBoundIterator<T, Comparator>::internal_iterator,
              TheorySolverBoundIterator<T, Comparator>::internal_iterator>
        nq_bounds)
    : begin_bounds_it_(bounds.first),
      bounds_it_(bounds.first),
      end_bounds_it_(bounds.second),
      begin_nq_bounds_it_(nq_bounds.first),
      nq_bounds_it_(nq_bounds.first),
      end_nq_bounds_it_(nq_bounds.second) {}
template <class T, class Comparator>
TheorySolverBoundIterator<T, Comparator>::TheorySolverBoundIterator(
    TheorySolverBoundIterator<T, Comparator>::internal_iterator begin_bounds_it,
    TheorySolverBoundIterator<T, Comparator>::internal_iterator end_bounds_it)
    : begin_bounds_it_(begin_bounds_it),
      bounds_it_(begin_bounds_it),
      end_bounds_it_(end_bounds_it),
      begin_nq_bounds_it_(end_bounds_it),
      nq_bounds_it_(end_bounds_it),
      end_nq_bounds_it_(end_bounds_it) {}
template <class T, class Comparator>
TheorySolverBoundIterator<T, Comparator>::TheorySolverBoundIterator(
    std::pair<TheorySolverBoundIterator<T, Comparator>::internal_iterator,
              TheorySolverBoundIterator<T, Comparator>::internal_iterator>
        bounds)
    : begin_bounds_it_(bounds.first),
      bounds_it_(bounds.first),
      end_bounds_it_(bounds.second),
      begin_nq_bounds_it_(bounds.second),
      nq_bounds_it_(bounds.second),
      end_nq_bounds_it_(bounds.second) {}

template <class T, class Comparator>
TheorySolverBoundIterator<T, Comparator> &TheorySolverBoundIterator<T, Comparator>::operator++() {
  if (bounds_it_ != end_bounds_it_) {
    ++bounds_it_;
  } else if (nq_bounds_it_ != end_nq_bounds_it_) {
    ++nq_bounds_it_;
  }
  return *this;
}

template <class T, class Comparator>
const TheorySolverBoundIterator<T, Comparator> TheorySolverBoundIterator<T, Comparator>::operator++(int) {
  TheorySolverBoundIterator tmp = *this;
  ++*this;
  return tmp;
}

template <class T, class Comparator>
TheorySolverBoundIterator<T, Comparator> &TheorySolverBoundIterator<T, Comparator>::operator--() {
  if (nq_bounds_it_ != begin_nq_bounds_it_) {
    --nq_bounds_it_;
  } else if (bounds_it_ != begin_bounds_it_) {
    --bounds_it_;
  }
  return *this;
}
template <class T, class Comparator>
const TheorySolverBoundIterator<T, Comparator> TheorySolverBoundIterator<T, Comparator>::operator--(int) {
  TheorySolverBoundIterator tmp = *this;
  --*this;
  return tmp;
}
template <class T, class Comparator>
typename TheorySolverBoundIterator<T, Comparator>::value_type TheorySolverBoundIterator<T, Comparator>::operator[](
    int i) const {
  const int distance = std::distance(begin_bounds_it_, end_bounds_it_);
  return i < distance ? *(bounds_it_ + i) : *(nq_bounds_it_ + i - distance);
}

template class TheorySolverBoundIterator<TheorySolverBoundVector::Bound, BoundComparator>;

}  // namespace dlinear