#include "BitIncrementIterator.h"

#include "dlinear/util/exception.h"

namespace dlinear {
BitIncrementIterator& BitIncrementIterator::operator++() {
    if (std::all_of(vector_.begin(), vector_.end(), [](bool b) { return b; })) {
    vector_.clear();
    return *this;
  }

  bool carry = vector_[vector_.size() - 1];
  vector_[vector_.size() - 1] = !vector_[vector_.size() - 1];
  for (int i = static_cast<int>(vector_.size()) - 2; carry && i >= 0; i--) {
    carry = vector_[i];
    vector_[i] = !vector_[i];
  }

  return *this;
}

BitIncrementIterator BitIncrementIterator::operator++(int) {
  BitIncrementIterator tmp(*this);
  operator++();
  return tmp;
}

}  // namespace dlinear