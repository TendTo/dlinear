/**
 * @file BitIncrementIterator.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "BitIncrementIterator.h"

#include "dlinear/util/exception.h"

namespace dlinear {

BitIncrementIterator &BitIncrementIterator::operator++() {
  if (IsDone()) {
    vector_.clear();
    return *this;
  }

  bool carry = vector_[vector_.size() - 1] || fixed_[vector_.size() - 1];
  if (!fixed_[vector_.size() - 1]) vector_[vector_.size() - 1] = !vector_[vector_.size() - 1];
  for (int i = static_cast<int>(vector_.size()) - 2; carry && i >= 0; i--) {
    carry = fixed_[i] ? carry : vector_[i];
    if (!fixed_[i]) vector_[i] = !vector_[i];
  }

  return *this;
}

BitIncrementIterator BitIncrementIterator::operator++(int) {
  BitIncrementIterator tmp(*this);
  operator++();
  return tmp;
}

bool BitIncrementIterator::Learn(size_t i) {
  if (fixed_[i]) return false;
  fixed_[i] = true;
  vector_[i] = !vector_[i];
  ResetNonFixed(i + 1);
  return true;
}

bool BitIncrementIterator::Learn(size_t i, bool value) {
  if (fixed_[i] && vector_[i] != value) return false;
  fixed_[i] = true;
  vector_[i] = value;
  ResetNonFixed(i + 1);
  return true;
}

bool BitIncrementIterator::IsDone() const {
  for (size_t i = 0; i < vector_.size(); i++) {
    if (!fixed_[i] && !vector_[i]) return false;
  }
  return true;
}

// TODO: smart reset
void BitIncrementIterator::ResetNonFixed(size_t start_pos) {
  for (size_t j = start_pos; j < vector_.size(); j++) {
    if (!fixed_[j]) vector_[j] = false;
  }
}

}  // namespace dlinear
