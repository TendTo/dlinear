/**
 * @file ScopedVector.hpp
 * @author dlinear
 * @date 14 Aug 2023
 * @copyright 2023 dlinear
 * @brief Backtrackable scoped vector.
 *
 * This is a vector that supports backtracking. It is used to store
 * intermediate results.
 */
#pragma once

#include <algorithm>
#include <cstddef>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

namespace dlinear {

template <typename T>
class ScopedVector {
 public:
  typedef std::vector<T> vector;
  typedef typename vector::value_type value_type;
  typedef typename vector::iterator iterator;
  typedef typename vector::const_iterator const_iterator;
  typedef typename vector::reverse_iterator reverse_iterator;
  typedef typename vector::const_reverse_iterator const_reverse_iterator;
  typedef typename vector::size_type size_type;
  typedef typename vector::reference reference;
  typedef typename vector::const_reference const_reference;

  ScopedVector() = default;
  ScopedVector(const ScopedVector &) = default;
  ScopedVector(ScopedVector &&) noexcept = default;
  ScopedVector &operator=(const ScopedVector &) = default;
  ScopedVector &operator=(ScopedVector &&) noexcept = default;
  ~ScopedVector() = default;

  iterator begin() { return vector_.begin(); }
  iterator end() { return vector_.end(); }
  const_iterator begin() const { return vector_.cbegin(); }
  const_iterator end() const { return vector_.cend(); }
  const_iterator cbegin() const { return vector_.cbegin(); }
  const_iterator cend() const { return vector_.cend(); }
  reverse_iterator rbegin() { return vector_.rbegin(); }
  reverse_iterator rend() { return vector_.rend(); }
  const_reverse_iterator rbegin() const { return vector_.crbegin(); }
  const_reverse_iterator rend() const { return vector_.crend(); }
  const_reverse_iterator crbegin() const { return vector_.crbegin(); }
  const_reverse_iterator crend() const { return vector_.crend(); }

  void push_back(value_type const &v) { vector_.push_back(v); }
  void push_back(value_type &&v) { vector_.push_back(std::move(v)); }
  void push() { scopes_.push_back(vector_.size()); }
  size_t pop() {
    if (scopes_.empty()) {
      throw std::runtime_error("Nothing to pop.");
    }
    size_t count = 0;
    size_t const prev_size = scopes_.back();
    scopes_.pop_back();
    size_t cur_size = vector_.size();
    while (cur_size-- > prev_size) {
      vector_.pop_back();
      count++;
    }
    return count;
  }

  [[nodiscard]] bool empty() const { return vector_.empty(); }
  [[nodiscard]] size_t size() const { return vector_.size(); }
  [[nodiscard]] vector const &get_vector() const { return vector_; }
  [[nodiscard]] vector get_vector() { return vector_; }

  reference first() { return vector_.at(0); }
  const_reference first() const { return vector_.at(0); }
  reference last() { return vector_.at(size() - 1); }
  const_reference last() const { return vector_.at(size() - 1); }
  reference operator[](size_type n) { return vector_[n]; }
  const_reference operator[](size_type n) const { return vector_[n]; }
  bool operator<(ScopedVector<T> const &v) const {
    for (size_t i = 0; i < vector_.size(); i++) {
      if (vector_[i] < v.vector_[i]) {
        return true;
      }
    }
    return false;
  }
  vector get_reverse() const {
    vector tmp = vector_;
    std::reverse(tmp.begin(), tmp.end());
    return tmp;
  }

  friend std::ostream &operator<<(std::ostream &os, ScopedVector<T> const &v) {
    for (auto const &e : v) os << e << std::endl;
    return os;
  }

 private:
  vector vector_;
  std::vector<size_t> scopes_;
};

}  // namespace dlinear
