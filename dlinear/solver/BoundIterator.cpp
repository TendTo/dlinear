/**
 * @file BoundIterator.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "BoundIterator.h"

#include <algorithm>
#include <compare>
#include <ostream>
#include <vector>

#include "dlinear/util/exception.h"

namespace dlinear {

const typename BoundIterator::vector_type BoundIterator::default_empty_vector_{};

BoundIterator::BoundIterator()
    : begin_bounds_it_(default_empty_vector_.cend()),
      bounds_it_(default_empty_vector_.cend()),
      end_bounds_it_(default_empty_vector_.cend()),
      begin_nq_bounds_it_(default_empty_vector_.cend()),
      nq_bounds_it_(default_empty_vector_.cend()),
      end_nq_bounds_it_(default_empty_vector_.cend()) {
  DLINEAR_ASSERT(begin_bounds_it_ <= bounds_it_ && bounds_it_ <= end_bounds_it_, "Bounds iterator is out of bounds.");
  DLINEAR_ASSERT(begin_nq_bounds_it_ <= nq_bounds_it_ && nq_bounds_it_ <= end_nq_bounds_it_,
                 "Non-equal bounds iterator is out of bounds.");
}

BoundIterator::BoundIterator(BoundIterator::internal_iterator begin_bounds_it,
                             BoundIterator::internal_iterator end_bounds_it,
                             BoundIterator::internal_iterator begin_nq_bounds_it,
                             BoundIterator::internal_iterator end_nq_bounds_it)
    : begin_bounds_it_(begin_bounds_it),
      bounds_it_(begin_bounds_it),
      end_bounds_it_(std::max(end_bounds_it, begin_bounds_it)),
      begin_nq_bounds_it_(begin_nq_bounds_it),
      nq_bounds_it_(begin_nq_bounds_it),
      end_nq_bounds_it_(std::max(end_nq_bounds_it, begin_nq_bounds_it)) {
  DLINEAR_ASSERT(begin_bounds_it_ <= bounds_it_ && bounds_it_ <= end_bounds_it_, "Bounds iterator is out of bounds.");
  DLINEAR_ASSERT(begin_nq_bounds_it_ <= nq_bounds_it_ && nq_bounds_it_ <= end_nq_bounds_it_,
                 "Non-equal bounds iterator is out of bounds.");
}

BoundIterator::BoundIterator(std::pair<BoundIterator::internal_iterator, BoundIterator::internal_iterator> bounds,
                             std::pair<BoundIterator::internal_iterator, BoundIterator::internal_iterator> nq_bounds)
    : begin_bounds_it_(bounds.first),
      bounds_it_(bounds.first),
      end_bounds_it_(std::max(bounds.second, bounds.first)),
      begin_nq_bounds_it_(nq_bounds.first),
      nq_bounds_it_(nq_bounds.first),
      end_nq_bounds_it_(std::max(nq_bounds.second, nq_bounds.first)) {
  DLINEAR_ASSERT(begin_bounds_it_ <= bounds_it_ && bounds_it_ <= end_bounds_it_, "Bounds iterator is out of bounds.");
  DLINEAR_ASSERT(begin_nq_bounds_it_ <= nq_bounds_it_ && nq_bounds_it_ <= end_nq_bounds_it_,
                 "Non-equal bounds iterator is out of bounds.");
}
BoundIterator::BoundIterator(BoundIterator::internal_iterator begin_bounds_it,
                             BoundIterator::internal_iterator end_bounds_it)
    : begin_bounds_it_(begin_bounds_it),
      bounds_it_(begin_bounds_it),
      end_bounds_it_(std::max(end_bounds_it, begin_bounds_it)),
      begin_nq_bounds_it_(default_empty_vector_.cend()),
      nq_bounds_it_(default_empty_vector_.cend()),
      end_nq_bounds_it_(default_empty_vector_.cend()) {
  DLINEAR_ASSERT(begin_bounds_it_ <= bounds_it_ && bounds_it_ <= end_bounds_it_, "Bounds iterator is out of bounds.");
  DLINEAR_ASSERT(begin_nq_bounds_it_ <= nq_bounds_it_ && nq_bounds_it_ <= end_nq_bounds_it_,
                 "Non-equal bounds iterator is out of bounds.");
}
BoundIterator::BoundIterator(std::pair<BoundIterator::internal_iterator, BoundIterator::internal_iterator> bounds)
    : begin_bounds_it_(bounds.first),
      bounds_it_(bounds.first),
      end_bounds_it_(std::max(bounds.second, bounds.first)),
      begin_nq_bounds_it_(default_empty_vector_.cend()),
      nq_bounds_it_(default_empty_vector_.cend()),
      end_nq_bounds_it_(default_empty_vector_.cend()) {
  DLINEAR_ASSERT(begin_bounds_it_ <= bounds_it_ && bounds_it_ <= end_bounds_it_, "Bounds iterator is out of bounds.");
  DLINEAR_ASSERT(begin_nq_bounds_it_ <= nq_bounds_it_ && nq_bounds_it_ <= end_nq_bounds_it_,
                 "Non-equal bounds iterator is out of bounds.");
}

BoundIterator &BoundIterator::operator++() {
  if (bounds_it_ != end_bounds_it_) {
    ++bounds_it_;
  } else if (nq_bounds_it_ != end_nq_bounds_it_) {
    ++nq_bounds_it_;
  }
  return *this;
}

const BoundIterator BoundIterator::operator++(int) {
  BoundIterator tmp = *this;
  ++*this;
  return tmp;
}

BoundIterator &BoundIterator::operator--() {
  if (nq_bounds_it_ != begin_nq_bounds_it_) {
    --nq_bounds_it_;
  } else if (bounds_it_ != begin_bounds_it_) {
    --bounds_it_;
  }
  return *this;
}
const BoundIterator BoundIterator::operator--(int) {
  BoundIterator tmp = *this;
  --*this;
  return tmp;
}
typename BoundIterator::value_type BoundIterator::operator[](int i) const {
  const int distance = std::distance(begin_bounds_it_, end_bounds_it_);
  return i < distance ? *(bounds_it_ + i) : *(nq_bounds_it_ + i - distance);
}

std::ostream &operator<<(std::ostream &os, const BoundIterator &violation) {
  BoundIterator it{violation.bounds(), violation.nq_bounds()};
  os << "BoundIterator{";
  for (size_t i = 0; it; ++it, ++i) {
    os << *it;
    if (i + 1 < it.size()) {
      os << ", ";
    }
  }
  return os << "}";
}

}  // namespace dlinear
