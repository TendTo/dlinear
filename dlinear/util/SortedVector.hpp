/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * SortedVector class.
 */
#pragma once

#include <algorithm>
#include <functional>
#include <iostream>
#include <iterator>
#include <utility>
#include <vector>

namespace dlinear {
struct Bound;  // Forward declaration

/**
 * Vector that maintains its elements sorted.
 *
 * This class is implemented as a wrapper around std::vector to provide a sorted list of elements.
 * Each time an element is inserted, it is placed in the correct position to maintain the sorted order.
 * @code
 * SortedVector<int> sorted_vector;
 * sorted_vector.insert(3);
 * sorted_vector.insert(1);
 * sorted_vector.insert(2);
 * for (const auto& value : sorted_vector) {
 *   std::cout << value << " ";
 * }
 * // Output: 1 2 3
 * @endcode
 * Using a custom comparison function is also supported:
 * @code
 * SortedVector<int, std::greater<>> sorted_vector;
 * sorted_vector.insert(3);
 * sorted_vector.insert(1);
 * sorted_vector.insert(2);
 * for (const auto& value : sorted_vector) {
 *   std::cout << value << " ";
 * }
 * // Output: 3 2 1
 * @endcode
 * @tparam T type of the elements in the sorted list
 * @tparam Compare comparison function to maintain the sorted order
 */
template <class T, class Compare = std::less<T>>
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

  /** @constructor{SortedVector} */
  SortedVector() = default;
  /**
   * Construct a new SortedVector object with the giver @p size.
   * @param size size of the sorted list.
   */
  explicit SortedVector(size_t size) : vector_(size) {}
  /**
   * Construct a new SortedVector object using an initializer @p list.
   *
   * The elements are placed in the correct position to maintain the sorted order.
   * @param list initializer list of elements
   */
  SortedVector(std::initializer_list<T> list) {
    vector_.reserve(list.size());
    for (const auto& value : list) insert(value);
  }

  /**
   * Insert an element with the provided @p value into the sorted list.
   *
   * The element is placed in the correct position to maintain the sorted order.
   * It returns an iterator to the inserted element.
   * @tparam V type of the element to insert
   * @param value value of the element to insert
   * @return iterator to the inserted element
   */
  template <typename V>
  iterator insert(V&& value) {
    auto it = std::lower_bound(vector_.cbegin(), vector_.cend(), value, compare_);
    return vector_.insert(it, std::forward<V>(value));
  }

  /**
   * Insert an element with the provided @p value into the sorted list.
   *
   * The element is placed in the correct position to maintain the sorted order.
   * It returns an iterator to the inserted element.
   * This version allows to specify if the element should be inserted in the lower or upper bound.
   * @tparam V type of the element to insert
   * @param value value of the element to insert
   * @param insert_lower if true, the element is inserted in the lower bound, otherwise in the upper bound
   * @return iterator to the inserted element
   */
  template <typename V>
  iterator insert(V&& value, bool insert_lower) {
    auto it = insert_lower ? std::lower_bound(vector_.cbegin(), vector_.cend(), value, compare_)
                           : std::upper_bound(vector_.cbegin(), vector_.cend(), value, compare_);
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
  iterator emplace(Args&&... args) {
    return insert(T(std::forward<Args>(args)...));
  }

  /**
   * Emplace a new element into the sorted list.
   *
   * The arguments are forwarded to the constructor of the element type.
   * The element is placed in the correct position to maintain the sorted order.
   * This version allows to specify if the element should be inserted in the lower or upper bound.
   * @param insert_lower if true, the element is inserted in the lower bound, otherwise in the upper bound
   * @param args arguments to forward to the constructor of the element type
   */
  template <typename... Args>
  iterator emplace(bool insert_lower, Args&&... args) {
    return insert(T(std::forward<Args>(args)...), insert_lower);
  }

  /** @getter{size, vector} */
  [[nodiscard]] size_t size() const { return vector_.size(); }

  /** @checker{emtpy, vector} */
  [[nodiscard]] bool empty() const { return vector_.empty(); }

  /**
   * Access element at index @p i with bounds checking.
   * @param i position of the element to access
   * @return element at the given position
   * @throw std::out_of_range if @p i is out of range
   */
  const T& at(size_t i) const {
    if (i >= vector_.size()) throw std::out_of_range("Index out of range");
    return vector_[i];
  }

  /**
   * Access element at index @p i with bounds checking.
   *
   * It also supports negative indices, where -1 is the last element, -2 is the second to last, and so on.
   * @param i position of the element to access (negative indices are supported)
   * @return element at the given position
   * @throw std::out_of_range if @p i is out of range
   */
  const T& at(int i) const {
    if (i < 0) i = static_cast<int>(vector_.size()) + i;
    if (i < 0 || i >= static_cast<int>(vector_.size())) throw std::out_of_range("Index out of range");
    return vector_[i];
  }

  /**
   * Direct access to the underlying vector.
   * @param i position of the element to access
   * @return element at the given position
   */
  const T& operator[](size_t i) const { return vector_[i]; }

  /**
   * Reference to the first element in the sorted list.
   * @return reference to the first element
   */
  const T& front() const { return vector_.front(); }

  /**
   * Reference to the last element in the sorted list.
   * @return reference to the last element
   */
  const T& back() const { return vector_.back(); }

  /**
   * Remove the element at position @p it from the sorted list.
   *
   * If the iterator is out of range, false is returned.
   * @param it iterator to the element to remove
   * @return true if the element has been removed
   * @return false if the element was not found
   */
  bool erase(const const_iterator& it) {
    if (it == vector_.end()) return false;
    vector_.erase(it);
    return true;
  }
  /**
   * Remove the element at index @p i from the sorted list.
   * If the index is out of range, false is returned.
   * @param i index of the element to remove
   * @return true if the element has been removed
   * @return false if the element was not found
   */
  bool erase(size_t i) {
    if (i >= vector_.size()) return false;
    vector_.erase(vector_.begin() + i);
    return true;
  }
  /**
   * Remove the element at index @p i from the sorted list.
   *
   * It also supports negative indices, where -1 is the last element, -2 is the second to last, and so on.
   * If the index is out of range, false is returned.
   * @param i index of the element to remove
   * @return true if the element has been removed
   * @return false if the element was not found
   */
  bool erase(int i) {
    if (i < 0) i = static_cast<int>(vector_.size()) - i;
    if (i < 0 || i >= static_cast<int>(vector_.size())) return false;
    vector_.erase(vector_.begin() + i);
    return true;
  }
  /**
   * Remove an element with the provided @p value from the sorted list.
   *
   * If multiple elements have the same @p value, only the first one is removed.
   * If the element is not found, false is returned.
   * @param value value of the element to remove
   * @return true if the element has been removed
   * @return false if the element was not found
   */
  bool erase_value(const T& value) {
    auto it = std::lower_bound(vector_.cbegin(), vector_.cend(), value, compare_);
    if (it == vector_.cend() || !IsEqual(*it, value)) return false;
    vector_.erase(it);
    return true;
  }

  /**
   * Find the index of an element with the provided @p value in the sorted list.
   *
   * If the element is not found, the end iterator is returned.
   * @param value value of the element to find
   * @return iterator to the element if it is found
   * @return end iterator if the element is not found
   */
  const_iterator find(const T& value) const {
    auto it = std::lower_bound(vector_.begin(), vector_.end(), value, compare_);
    if (it == vector_.end() || !IsEqual(*it, value)) return end();
    return it;
  }

  /**
   * Find the first position in which an element with the provided @p value could be inserted
   * without changing the ordering.
   *
   * It is equivalent to using std::lower_bound with the @p Compare function.
   * @param value value of the element to find
   * @return iterator to the first valid position
   */
  const_iterator lower_bound(const T& value) const {
    return std::lower_bound(vector_.begin(), vector_.end(), value, compare_);
  }

  /**
   * Find the last position in which an element with the provided @p value could be inserted
   * without changing the ordering.
   *
   * It is equivalent to using std::upper_bound with the @p Compare function.
   * @param value value of the element to find
   * @return iterator to the last valid position
   */
  const_iterator upper_bound(const T& value) const {
    return std::upper_bound(vector_.begin(), vector_.end(), value, compare_);
  }

  /**
   * Count the number of occurrences of an element with the provided @p value in the sorted list.
   *
   * If the element is not found, 0 is returned.
   * @param value value of the element to count
   * @return number of occurrences of the element in the sorted list
   */
  [[nodiscard]] size_t count(const T& value) const {
    auto it = find(value);
    if (it == vector_.end()) return 0;
    size_t count = 1;
    for (it++; it != vector_.end() && IsEqual(*it, value); ++it) ++count;
    return count;
  }

  /**
   * Check if the element with the provided @p value is contained in the vector.
   * @param value value of the element to search
   * @return true if the element is present
   * @return false if the element is not present
   */
  [[nodiscard]] bool contains(const T& value) const { return find(value) != end(); }

  /**
   * Find the last element in the vector with a value lesser than @p value
   * and return an iterator to the position after that one.
   * @param value upper bound for the search
   * @return iterator to the position after the last element with value less than @p value
   */
  [[nodiscard]] const_iterator lesser_end(const T& value) const {
    return std::lower_bound(vector_.begin(), vector_.end(), value, compare_);
  }

  /**
   * Find the first element in the vector with a value greater than @p value
   * and return an iterator to its position.
   * @param value lower bound for the search
   * @return iterator to the first element with value less than @p value
   */
  [[nodiscard]] const_iterator greater_begin(const T& value) const {
    auto it = std::upper_bound(vector_.begin(), vector_.end(), value, compare_);
    while (it != vector_.cend() && IsEqual(*it, value)) ++it;
    return it;
  }

  /** Clear the sorted list, removing all elements. */
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
  /**
   * Use the @ref compare_ function to check if two elements are equal.
   *
   * Since the function only checks ordering, to make sure two elements are equal @ref compare_ must be used twice.
   * @param lhs left-hand side element
   * @param rhs right-hand side element
   * @return true if the elements are equal
   * @return false if the elements are not equal
   */
  inline bool IsEqual(const T& lhs, const T& rhs) const { return !compare_(lhs, rhs) && !compare_(rhs, lhs); }

  std::vector<T> vector_;  ///< Underlying vector to store the sorted list
  Compare compare_;        ///< Comparison function to maintain the sorted order
};

template <typename T>
std::ostream& operator<<(std::ostream& os, const SortedVector<T>& it) {
  std::copy(it.cbegin(), std::prev(it.cend()), std::ostream_iterator<T>(os, ", "));
  return os << *(it.crbegin());
}

extern template class SortedVector<Bound>;
extern template class SortedVector<int>;
extern template class SortedVector<double>;

}  // namespace dlinear
