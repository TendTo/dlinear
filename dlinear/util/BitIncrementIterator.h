#pragma once

#include <algorithm>
#include <iterator>
#include <vector>

namespace dlinear {

class BitIncrementIterator {
 public:
  using iterator_category = std::input_iterator_tag;
  using value_type = std::vector<bool>;
  using reference = value_type const &;
  using pointer = value_type const *;
  using difference_type = ptrdiff_t;

  explicit BitIncrementIterator(int n) : vector_(n, false) {}
  explicit BitIncrementIterator(size_t n) : vector_(n, false) {}

  explicit operator bool() const { return !vector_.empty(); }

  pointer operator->() const { return &vector_; }
  reference operator*() const { return vector_; }

  bool operator==(const BitIncrementIterator &rhs) const { return vector_ == rhs.vector_; }
  bool operator!=(const BitIncrementIterator &rhs) const { return vector_ != rhs.vector_; }

  BitIncrementIterator &operator++();

  BitIncrementIterator operator++(int);

 private:
  std::vector<bool> vector_;
};

}  // namespace dlinear
