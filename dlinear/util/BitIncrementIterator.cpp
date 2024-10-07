/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "BitIncrementIterator.h"

#include <iostream>
#include <utility>

namespace dlinear {

std::vector<bool> &operator++(std::vector<bool> &vector) {
  if (vector.empty()) return vector;
  bool carry = vector[vector.size() - 1];
  vector[vector.size() - 1] = !vector[vector.size() - 1];
  for (int i = static_cast<int>(vector.size()) - 2; carry && i >= 0; i--) {
    carry = vector[i];
    vector[i] = !vector[i];
  }
  return vector;
}

std::vector<bool> &operator--(std::vector<bool> &vector) {
  if (vector.empty()) return vector;
  bool carry = !vector[vector.size() - 1];
  vector[vector.size() - 1] = !vector[vector.size() - 1];
  for (int i = static_cast<int>(vector.size()) - 2; carry && i >= 0; i--) {
    carry = !vector[i];
    vector[i] = !vector[i];
  }
  return vector;
}

BitIncrementIterator::BitIncrementIterator(std::vector<bool> starting_value)
    : vector_{starting_value},
      fixed_(starting_value.size(), false),
      starting_vector_{starting_value},
      ending_vector_{std::move(starting_value)} {
  --ending_vector_;
}

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

const BitIncrementIterator BitIncrementIterator::operator++(int) {
  BitIncrementIterator tmp(*this);
  operator++();
  return tmp;
}

BitIncrementIterator &BitIncrementIterator::operator--() {
  if (IsDone()) {
    vector_.clear();
    return *this;
  }

  bool carry = !vector_[vector_.size() - 1] || fixed_[vector_.size() - 1];
  if (!fixed_[vector_.size() - 1]) vector_[vector_.size() - 1] = !vector_[vector_.size() - 1];
  for (int i = static_cast<int>(vector_.size()) - 2; carry && i >= 0; i--) {
    carry = fixed_[i] ? carry : !vector_[i];
    if (!fixed_[i]) vector_[i] = !vector_[i];
  }

  return *this;
}
const BitIncrementIterator BitIncrementIterator::operator--(int) {
  BitIncrementIterator tmp{*this};
  operator--();
  return tmp;
}

bool BitIncrementIterator::operator[](size_t i) const { return vector_[i]; }

bool BitIncrementIterator::Learn(size_t i) {
  if (fixed_[i]) return false;
  UpdateVector(i, !vector_[i]);
  fixed_[i] = true;
  return true;
}

bool BitIncrementIterator::Learn(size_t i, bool value) {
  if (fixed_[i] && vector_[i] != value) return false;
  if (vector_[i] != value) UpdateVector(i, value);
  fixed_[i] = true;
  return true;
}

bool BitIncrementIterator::IsDone() const {
  // The vector is NOT done if at least one non-fixed bit is different from the corresponding ending vector value
  for (size_t i = 0; i < vector_.size(); i++) {
    if (!fixed_[i] && vector_[i] != ending_vector_[i]) return false;
  }
  return true;
}

void BitIncrementIterator::ResetNonFixedRight(size_t start_pos) {
  for (size_t i = start_pos; i < vector_.size(); i++) {
    if (!fixed_[i]) vector_[i] = starting_vector_[i];
  }
}

void BitIncrementIterator::ResetNonFixedLeft(size_t start_pos) {
  for (int i = static_cast<int>(start_pos); i >= 0; i--) {
    if (!fixed_[i]) vector_[i] = starting_vector_[i];
  }
}

void BitIncrementIterator::ResetNonFixed() {
  for (size_t i = 0; i < vector_.size(); i++) {
    if (!fixed_[i]) vector_[i] = starting_vector_[i];
  }
}

void BitIncrementIterator::UpdateVector(size_t i, bool value) {
  if (value && ending_vector_[i]) {  // The bit True has been learned and the ending vector bit is True
    while (!vector_[i]) ++(*this);
  } else if (value && !ending_vector_[i]) {
    ResetNonFixedRight(i + 1);
  } else if (ending_vector_[i]) {  // The bit False has been learned and the ending vector bit is True
    ResetNonFixed();
  } else {  // The bit False has been learned and the ending vector bit is False
    while (vector_[i]) ++(*this);
  }
  vector_[i] = value;
}

std::ostream &operator<<(std::ostream &os, const BitIncrementIterator &it) {
  std::copy(it->begin(), std::prev(it->end()), std::ostream_iterator<bool>(os, ", "));
  return os << *(it->rbegin());
}

}  // namespace dlinear
