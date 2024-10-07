/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * BitIncrementIterator class.
 *
 * It implements an abstraction used to iterate over all the possible bit vectors of a given size.
 */
#pragma once

#include <algorithm>
#include <cstddef>
#include <iosfwd>
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
 * The default behaviour of this class ensures `full-exploration-guarantee`: all possible
 * configuration the bit vector can be in will be explored.
 * Using any @ref Learn method will continue to maintain the guarantee over the now halved configuration space, but
 * some previously visited configuration may appear again.
 * @code
 * // Example learn:
 * BitIncrementIterator it(3);
 * it.Learn(1, true); // Fix the second bit to 1
 * for (; it; ++it) {
 *   for (bool b : *it) {
 *     std::cout << b;
 *   }
 *   std::cout << ", ";
 * }
 * std::cout << std::endl;
 * // Output:
 * // 010, 011, 110, 111,
 * @endcode
 * @warning Any manual alteration of the vector invalidates the guarantee.
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
  explicit BitIncrementIterator(std::size_t n)
      : vector_(n, false), fixed_(n, false), starting_vector_(n, false), ending_vector_(n, true) {}
  /**
   * Construct a new BitIncrementIterator object.
   *
   * The vector is initialized with the value of @p starting_value.
   * After enumerating all possible boolean vectors, the iterator will terminate and the vector will be cleared.
   * @param starting_value vector of booleans to initialize the iterator with
   */
  explicit BitIncrementIterator(std::vector<bool> starting_value);

  explicit operator bool() const { return !vector_.empty(); }

  pointer operator->() const { return &vector_; }
  reference operator*() const { return vector_; }

  bool operator==(const BitIncrementIterator &rhs) const { return vector_ == rhs.vector_; }
  bool operator!=(const BitIncrementIterator &rhs) const { return vector_ != rhs.vector_; }

  BitIncrementIterator &operator++();
  const BitIncrementIterator operator++(int);

  BitIncrementIterator &operator--();
  const BitIncrementIterator operator--(int);

  bool operator[](std::size_t i) const;

  /**
   * Check if the bit at position @p i is fixed.
   *
   * A bit is fixed if it is set to a specific value using the @ref Learn method.
   * A fixed bit's value cannot be changed anymore by the increment operation.
   * @param i index of the bit to check. The index must be in the range [0, n), big endian order.
   * @return true if the bit is fixed
   * @return false if the bit is not fixed
   * @throw std::out_of_range if @p i is out of range
   */
  [[nodiscard]] bool IsFixed(std::size_t i) const { return fixed_[i]; }

  /**
   * Set the @p i 't bit of the vector to @p value.
   *
   * If the bit was fixed, no operation will be performed unless @p force is specified.
   * @warning Using this method means losing the `full-exploration-guarantee`.
   * @param i index of the bit to change
   * @param value new value of the bit
   * @param force whether to ignore if the bit is fixed. This will not change it's fixed status
   */
  void Set(std::size_t i, bool value, bool force = false) { vector_[i] = force || !fixed_[i] ? value : vector_[i]; }

  /**
   * Set whether the @p i 'th bit of the vector is fixed.
   *
   * @warning Using this method means losing the `full-exploration-guarantee`.
   * @param i index of the bit to make fixed or un-fixed
   * @param fixed whether the bit should be fixed or not
   */
  void SetFixed(std::size_t i, bool fixed) { fixed_[i] = fixed; }

  /**
   * Learn the value of the bit at position @p i by inverting the bit.
   *
   * Invert the bit at position @p i and fix it to the new value.
   * A fixed bit's value cannot be changed anymore by the increment operation.
   * @note Other vector's values may change to maintain the `full-exploration-guarantee`.
   * If you want to avoid this behaviour, use @ref Set and @ref SetFixed manually.
   * @note Some previously visited configuration may appear again.
   * @param i index of the bit to check. The index must be in the range [0, n), big endian order.
   * @return true if the bit has been fixed
   * @return false if the bit was already fixed
   * @throw std::out_of_range if @p i is out of range
   */
  bool Learn(std::size_t i);
  /**
   * Learn the value of the bit at position @p i by setting the bit to @p value.
   *
   * Set the value of the bit at position @p i to @p value and fix it to the new value.
   * A fixed bit's value cannot be changed anymore by the increment operation.
   * @note Other vector's values may change to maintain the `full-exploration-guarantee`.
   * If you want to avoid this behaviour, use @ref Set and @ref SetFixed manually.
   * @note Some previously visited configuration may appear again.
   * @param i index of the bit to check. The index must be in the range [0, n), big endian order.
   * @param value value to set the bit to
   * @return true if the bit has now value @p value
   * @return false if the bit was already fixed and therefore not changed
   * @throw std::out_of_range if @p i is out of range
   */
  bool Learn(std::size_t i, bool value);

 private:
  /**
   * Reset all the non-fixed bits to the right of @p start_pos to their starting value.
   * @param start_pos starting position. The index must be in the range [0, n), big endian order.
   */
  void ResetNonFixedRight(std::size_t start_pos = 0);
  /**
   * Reset all the non-fixed bits to the left of @p start_pos to their starting value.
   * @param start_pos starting position. The index must be in the range [0, n), big endian order.
   */
  void ResetNonFixedLeft(std::size_t start_pos);
  /**
   * Reset all the non-fixed bits in the vector to their starting value.
   */
  void ResetNonFixed();
  /**
   * Check if the iterator is done.
   *
   * This happens when the vector is filled with true in every non-fixed position.
   * @return true if the iterator is done
   * @return false if the iterator is not done
   */
  [[nodiscard]] bool IsDone() const;

  /**
   * After a @ref Learn operation to set the @p i 'th bit to @p value, update the vector.
   *
   * Set the @p i 'th bit to @p value, potentially modifying the vector in order to ensure a full exploration.
   * @param i index of the bit to set
   * @param value new value of the bit
   */
  void UpdateVector(std::size_t i, bool value);

  std::vector<bool> vector_;           ///< The bit vector that will assume all the possible values.
  std::vector<bool> fixed_;            ///< Vector to indicate the fixed bits.
  std::vector<bool> starting_vector_;  ///< Vector to store the starting value of the iterator.
  std::vector<bool> ending_vector_;    ///< Vector to store the ending value of the iterator.
};

std::vector<bool> &operator++(std::vector<bool> &vector);
std::vector<bool> &operator--(std::vector<bool> &vector);
std::ostream &operator<<(std::ostream &os, const BitIncrementIterator &it);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::BitIncrementIterator)

#endif
