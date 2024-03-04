/**
 * @file SortedVector.hpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Simple sorted vector implementation.
 *
 * This class is implemented as a wrapper around std::vector to provide a sorted list of elements.
 */
#pragma once

#include <algorithm>
#include <iostream>
#include <vector>

namespace dlinear {

/**
 * SortedVector class.
 *
 * This class is implemented as a wrapper around std::vector to provide a sorted list of elements.
 * Each time an element is inserted, it is placed in the correct position to maintain the sorted order.
 * @code
 * SortedVector<int> sorted_vector;
 * sorted_vector.insert(3);
 * sorted_vector.insert(1);
 * sorted_vector.insert(2);
 * for (const auto& value : sorted_vector) {
 *  std::cout << value << " ";
 * }
 * // Output: 1 2 3
 * @endcode
 * @tparam T type of the elements in the sorted list
 */
template <typename T>
class SortedVector {
 public:
  using value_type = T;                                ///< Type of the elements in the sorted list
  using size_type = size_t;                            ///< Type of the size of the sorted list
  using difference_type = std::ptrdiff_t;              ///< Type of the difference between two iterators
  using reference = T&;                                ///< Type of the reference to an element in the sorted list
  using const_reference = const T&;                    ///< Type of the const reference to an element in the sorted list
  using pointer = T*;                                  ///< Type of the pointer to an element in the sorted list
  using const_pointer = const T*;                      ///< Type of the const pointer to an element in the sorted list
  using iterator = typename std::vector<T>::iterator;  ///< Type of the iterator to the sorted list
  using const_iterator = typename std::vector<T>::const_iterator;  ///< Type of the const iterator to the sorted list
  using reverse_iterator =
      typename std::vector<T>::reverse_iterator;  ///< Type of the reverse iterator to the sorted list
  using const_reverse_iterator =
      typename std::vector<T>::const_reverse_iterator;  ///< Type of the const reverse iterator to the sorted list

  /**
   * Default constructor.
   */
  SortedVector() = default;
  /**
   * Constructor with a given size.
   * @param size size of the sorted list.
   */
  explicit SortedVector(size_t size) : vector_(size) {}
  /**
   * Constructor with using an initializer list.
   *
   * The elements are placed in the correct position to maintain the sorted order.
   * @param ilist initializer list of elements
   */
  SortedVector(std::initializer_list<T> ilist) {
    for (const auto& value : ilist) insert(value);
  }

  /**
   * Insert an element into the sorted list.
   *
   * The element is placed in the correct position to maintain the sorted order.
   * It returns an iterator to the inserted element.
   * @param value element to insert
   * @return iterator to the inserted element
   */
  template <typename V>
  iterator insert(V&& value) {
    auto it = std::lower_bound(vector_.cbegin(), vector_.cend(), value);
    return vector_.insert(it, std::forward<V>(value));
  }

  /**
   * Emplace a new element into the sorted list.
   *
   * The arguments are forwarded to the constructor of the element type.
   * The element is placed in the correct position to maintain the sorted order.
   * @param args arguments to forward to the constructor of the element type
   */
  template <typename... Args>
  void emplace(Args&&... args) {
    insert(std::forward<Args>(args)...);
  }

  /**
   * Size of the sorted list.
   * @return size of the sorted list
   */
  [[nodiscard]] size_t size() const { return vector_.size(); }

  /**
   * Check if the sorted list is empty.
   * @return true if the sorted list is empty
   * @return false if the sorted list is not empty
   */
  [[nodiscard]] bool empty() const { return vector_.empty(); }

  /**
   * Access element at a given position with bounds checking.
   * @param pos position of the element to access
   * @return element at the given position
   */
  T at(size_t pos) const {
    if (pos >= vector_.size()) throw std::out_of_range("Index out of range");
    return vector_[pos];
  }

  /**
   * Access element at a given position with bounds checking.
   *
   * It also supports negative indices, where -1 is the last element, -2 is the second to last, and so on.
   * @param pos position of the element to access (negative indices are supported)
   * @return element at the given position
   */
  T at(int pos) const {
    if (pos < 0) pos = static_cast<int>(vector_.size()) + pos;
    if (pos < 0 || pos >= static_cast<int>(vector_.size())) throw std::out_of_range("Index out of range");
    return vector_[pos];
  }

  /**
   * Direct access to the underlying vector.
   * @param pos position of the element to access
   * @return element at the given position
   */
  T operator[](size_t pos) const { return vector_[pos]; }

  /**
   * Remove an element from the sorted list.
   * @param pos index of the element to remove
   */
  bool erase(size_t pos) {
    if (pos >= vector_.size()) return false;
    vector_.erase(vector_.begin() + pos);
    return true;
  }
  /**
   * Remove an element from the sorted list.
   *
   * It also supports negative indices, where -1 is the last element, -2 is the second to last, and so on.
   * @param pos index of the element to remove
   */
  bool erase(int pos) {
    if (pos < 0) pos = static_cast<int>(vector_.size()) - pos;
    if (pos < 0 || pos >= static_cast<int>(vector_.size())) return false;
    vector_.erase(vector_.begin() + pos);
    return true;
  }
  /**
   * Remove an element from the sorted list.
   *
   * If multiple elements have the same value, only the first one is removed.
   * If the element is not found, false is returned.
   * @param value element to remove
   * @return true if the element is removed
   * @return false if the element was not found
   */
  bool erase_value(const T& value) {
    auto it = std::lower_bound(vector_.cbegin(), vector_.cend(), value);
    if (it == vector_.cend() || *it != value) return false;
    vector_.erase(it);
    return true;
  }

  /**
   * Find the index of an element in the sorted list.
   *
   * If the element is not found, -1 is returned.
   * @param value element to find
   * @return index of the element in the sorted list
   * @return -1 if the element is not found
   */
  const_iterator find(const T& value) const {
    auto it = std::lower_bound(vector_.begin(), vector_.end(), value);
    if (it == vector_.end() || *it != value) return end();
    return it;
  }

  /**
   * Count the number of occurrences of an element in the sorted list.
   *
   * If the element is not found, 0 is returned.
   * @param value element to count
   * @return number of occurrences of the element in the sorted list
   */
  [[nodiscard]] size_t count(const T& value) const {
    auto it = find(value);
    if (it == vector_.end()) return 0;
    size_t count = 1;
    for (it++; it != vector_.end() && *it == value; ++it) ++count;
    return count;
  }

  /**
   * Clear the sorted list.
   */
  void clear() { vector_.clear(); }

  iterator begin() { return vector_.begin(); }
  iterator end() { return vector_.end(); }
  const_iterator begin() const { return vector_.cbegin(); }
  const_iterator end() const { return vector_.cend(); }
  const_iterator cbegin() const { return vector_.begin(); }
  const_iterator cend() const { return vector_.end(); }
  reverse_iterator rbegin() { return vector_.rbegin(); }
  reverse_iterator rend() { return vector_.rend(); }
  const_reverse_iterator rbegin() const { return vector_.crbegin(); }
  const_reverse_iterator rend() const { return vector_.crend(); }
  const_reverse_iterator crbegin() const { return vector_.crbegin(); }
  const_reverse_iterator crend() const { return vector_.crend(); }

 private:
  std::vector<T> vector_;  ///< Underlying vector to store the sorted list
};

template <typename T>
std::ostream& operator<<(std::ostream& os, const SortedVector<T>& it) {
  std::copy(it->begin(), std::prev(it->end()), std::ostream_iterator<T>(os, ", "));
  return os << *(it->rbegin());
}

}  // namespace dlinear
