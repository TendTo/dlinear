/**
 * @file BitIncrementIterator.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief BitIncrementIterator class.
 *
 * It implements an abstraction used to iterate over all the possible bit vectors of a given size.
 */
#pragma once

#include <algorithm>
#include <iterator>
#include <vector>

namespace dlinear {

/**
 * BitIncrementIterator class
 *
 * The @ref BitIncrementIterator class is an abstraction used to iterate over all the possible bit vectors of a given
 * size. It stores a vector of booleans and each time it is incremented, it changes the vector to the next possible bit
 * vector. The result simulates the increment operation of a binary number. If the iterator is incremented when boolean
 * vector if filled with true, the vector itself is cleared and the iterator is considered done.
 * @code
 * // Example usage:
 * for (BitIncrementIterator it(3); it; ++it) {
 *   for (bool b : *it) {
 *     std::cout << b;
 *   }
 *   std::cout << ", ";
 * }
 * std::cout << std::endl;
 * // Output:
 * // 000, 001, 010, 011, 100, 101, 110, 111,
 * @endcode
 */
class BitIncrementIterator {
 public:
  using iterator_category = std::input_iterator_tag;
  using value_type = std::vector<bool>;
  using reference = value_type const &;
  using pointer = value_type const *;
  using difference_type = ptrdiff_t;

  /**
   * Construct a new BitIncrementIterator object.
   *
   * The vector is initialized with @p n bits set to false.
   * If @p n is 0, the vector is empty and is considered done immediately.
   * @param n number of bits in the vector
   */
  explicit BitIncrementIterator(size_t n) : vector_(n, false), fixed_(n, false) {}

  explicit operator bool() const { return !vector_.empty(); }

  pointer operator->() const { return &vector_; }
  reference operator*() const { return vector_; }

  bool operator==(const BitIncrementIterator &rhs) const { return vector_ == rhs.vector_; }
  bool operator!=(const BitIncrementIterator &rhs) const { return vector_ != rhs.vector_; }

  BitIncrementIterator &operator++();

  BitIncrementIterator operator++(int);

  /**
   * Check if the bit at position @p i is fixed.
   *
   * A bit is fixed if it is set to a specific value using the @ref Learn method.
   * A fixed bit's value cannot be changed anymore by the increment operation.
   * @param i index of the bit to check. The index must be in the range [0, n), big endian order.
   * @return true if the bit is fixed
   * @return false if the bit is not fixed
   * @throws std::out_of_range if @p i is out of range
   */
  [[nodiscard]] bool IsFixed(size_t i) const { return fixed_[i]; }

  /**
   * Learn the value of the bit at position @p i by inverting the bit.
   *
   * Invert the bit at position @p i and fix it to the new value.
   * A fixed bit's value cannot be changed anymore by the increment operation.
   * All the bits to the right of the fixed bit are reset to false.
   * @param i index of the bit to check. The index must be in the range [0, n), big endian order.
   * @return true if the bit has been fixed
   * @return false if the bit was already fixed
   * @throws std::out_of_range if @p i is out of range
   */
  bool Learn(size_t i);
  /**
   * Learn the value of the bit at position @p i by setting the bit to @value.
   *
   * Set the value of the bit at position @p i to @value and fix it to the new value.
   * A fixed bit's value cannot be changed anymore by the increment operation.
   * All the bits to the right of the fixed bit are reset to false.
   * @param i index of the bit to check. The index must be in the range [0, n), big endian order.
   * @param value value to set the bit to
   * @return true if the bit has now value @p value
   * @return false if the bit was already fixed and therefore not changed
   * @throws std::out_of_range if @p i is out of range
   */
  bool Learn(size_t i, bool value);

 private:
  /**
   * Reset all the non-fixed bits to the right of @p start_pos to false.
   * @param start_pos starting position. The index must be in the range [0, n), big endian order.
   * @throws std::out_of_range if @p start_pos is out of range
   */
  void ResetNonFixed(size_t start_pos = 0);
  /**
   * Check if the iterator is done.
   *
   * This happens when the vector is filled with true in every non-fixed position.
   * @return true if the iterator is done
   * @return false if the iterator is not done
   */
  [[nodiscard]] bool IsDone() const;

  std::vector<bool> vector_;  ///< The bit vector that will assume all the possible values.
  std::vector<bool> fixed_;   ///< Vector to indicate the fixed bits.
};

}  // namespace dlinear
