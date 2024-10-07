/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * NumericDataContainer class.
 *
 * Simple class that holds a numeric value and a data value.
 * It is used to take advantage of the strong ordering and equality operators of the numeric value,
 * as well as the arithmetic operators, while still being able to store additional data.
 */
#pragma once

#include <iostream>
#include <type_traits>
#include <utility>

#include "dlinear/util/concepts.h"

namespace dlinear {

/**
 * NumericDataContainer class.
 *
 * Simple class that holds a numeric value and a data value.
 * It is used to take advantage of the strong ordering and equality operators of the numeric value,
 * as well as the arithmetic operators, while still being able to store additional data.
 * @tparam N numeric type used for comparison and arithmetic operations
 * @tparam D generic data type
 */
template <Numeric N, std::default_initializable D>
struct NumericDataContainer {
  using NumericType = N;
  using DataType = D;

  NumericDataContainer() : numeric{0}, data{} {}
  explicit NumericDataContainer(N input_numeric) : numeric{input_numeric}, data{} {}
  NumericDataContainer(N input_numeric, D input_data) : numeric{input_numeric}, data{input_data} {}

  template <std::convertible_to<N> T>
  std::strong_ordering operator<=>(const NumericDataContainer<T, D> &rhs) const {
    return numeric < static_cast<N>(rhs.numeric)   ? std::strong_ordering::less
           : numeric > static_cast<N>(rhs.numeric) ? std::strong_ordering::greater
                                                   : std::strong_ordering::equal;
  }
  template <std::convertible_to<N> T>
  bool operator==(const NumericDataContainer<T, D> &rhs) const {
    return numeric == N{rhs.numeric};
  }

  template <std::convertible_to<N> T>
  std::strong_ordering operator<=>(const T &rhs) const {
    return numeric < static_cast<N>(rhs)   ? std::strong_ordering::less
           : numeric > static_cast<N>(rhs) ? std::strong_ordering::greater
                                           : std::strong_ordering::equal;
  }
  template <std::convertible_to<N> T>
  bool operator==(const T &rhs) const {
    return numeric == N{rhs};
  }

  bool EqualTo(const NumericDataContainer<N, D> &rhs) const { return numeric == rhs.numeric && data == rhs.data; }

  template <std::convertible_to<N> T>
  NumericDataContainer &operator+=(const NumericDataContainer<T, D> &rhs) {
    numeric += N{rhs.numeric};
    return *this;
  }
  template <std::convertible_to<N> T>
  NumericDataContainer &operator-=(const NumericDataContainer<T, D> &rhs) {
    numeric -= N{rhs.numeric};
    return *this;
  }
  template <std::convertible_to<N> T>
  NumericDataContainer &operator*=(const NumericDataContainer<T, D> &rhs) {
    numeric *= N{rhs.numeric};
    return *this;
  }
  template <std::convertible_to<N> T>
  NumericDataContainer &operator/=(const NumericDataContainer<T, D> &rhs) {
    numeric /= N{rhs.numeric};
    return *this;
  }

  template <std::convertible_to<N> T>
  NumericDataContainer &operator+=(const T &rhs) {
    numeric += N{rhs};
    return *this;
  }
  template <std::convertible_to<N> T>
  NumericDataContainer &operator-=(const T &rhs) {
    numeric -= N{rhs};
    return *this;
  }
  template <std::convertible_to<N> T>
  NumericDataContainer &operator*=(const T &rhs) {
    numeric *= N{rhs};
    return *this;
  }
  template <std::convertible_to<N> T>
  NumericDataContainer &operator/=(const T &rhs) {
    numeric /= N{rhs};
    return *this;
  }

  template <std::convertible_to<N> T>
  NumericDataContainer operator+(const NumericDataContainer<T, D> &rhs) const {
    return {numeric + N{rhs.numeric}, data};
  }
  template <std::convertible_to<N> T>
  NumericDataContainer operator-(const NumericDataContainer<T, D> &rhs) const {
    return {numeric - N{rhs.numeric}, data};
  }
  template <std::convertible_to<N> T>
  NumericDataContainer operator*(const NumericDataContainer<T, D> &rhs) const {
    return {numeric * N{rhs.numeric}, data};
  }
  template <std::convertible_to<N> T>
  NumericDataContainer operator/(const NumericDataContainer<T, D> &rhs) const {
    return {numeric / N{rhs.numeric}, data};
  }

  template <std::convertible_to<N> T>
  NumericDataContainer operator+(const T &rhs) const {
    return {numeric + N{rhs}, data};
  }
  template <std::convertible_to<N> T>
  NumericDataContainer operator-(const T &rhs) const {
    return {numeric - N{rhs}, data};
  }
  template <std::convertible_to<N> T>
  NumericDataContainer operator*(const T &rhs) const {
    return {numeric * N{rhs}, data};
  }
  template <std::convertible_to<N> T>
  NumericDataContainer operator/(const T &rhs) const {
    return {numeric / N{rhs}, data};
  }

  NumericDataContainer operator-() const { return {-numeric, data}; }

  NumericDataContainer &operator++() {
    ++numeric;
    return *this;
  }
  const NumericDataContainer operator++(int) {
    NumericDataContainer tmp(*this);
    operator++();
    return tmp;
  }
  NumericDataContainer &operator--() {
    --numeric;
    return *this;
  }
  const NumericDataContainer operator--(int) {
    NumericDataContainer tmp(*this);
    operator--();
    return tmp;
  }

  N numeric;
  D data;
};

template <class N, class D, class T>
NumericDataContainer<N, D> operator+(const T &lhs, const NumericDataContainer<N, D> &rhs) {
  return {N{lhs} + rhs.numeric, rhs.data};
}
template <class N, class D, class T>
NumericDataContainer<N, D> operator-(const T &lhs, const NumericDataContainer<N, D> &rhs) {
  return {N{lhs} - rhs.numeric, rhs.data};
}
template <class N, class D, class T>
NumericDataContainer<N, D> operator*(const T &lhs, const NumericDataContainer<N, D> &rhs) {
  return {N{lhs} * rhs.numeric, rhs.data};
}
template <class N, class D, class T>
NumericDataContainer<N, D> operator/(const T &lhs, const NumericDataContainer<N, D> &rhs) {
  return {N{lhs} / rhs.numeric, rhs.data};
}

template <class N, class D, class T>
std::strong_ordering operator<=>(const T &lhs, const NumericDataContainer<N, D> &rhs) {
  return static_cast<N>(lhs) < rhs.numeric   ? std::strong_ordering::less
         : static_cast<N>(lhs) > rhs.numeric ? std::strong_ordering::greater
                                             : std::strong_ordering::equal;
}

template <class N, class D>
std::ostream &operator<<(std::ostream &os, const NumericDataContainer<N, D> &ndc) {
  return os << "{" << ndc.numeric << ", " << ndc.data << "}";
}

}  // namespace dlinear
