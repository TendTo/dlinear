#pragma once

#include <concepts>
#include <iostream>
#include <type_traits>
#include <utility>

template <class T>
concept Numeric = std::totally_ordered<T> && requires(T a, T b) {
  { a + b } -> std::convertible_to<T>;
  { a - b } -> std::convertible_to<T>;
  { a * b } -> std::convertible_to<T>;
  { a / b } -> std::convertible_to<T>;
};

namespace dlinear {

template <Numeric N, class D>
struct NumericDataContainer {
  using NumericType = N;
  using DataType = D;

  NumericDataContainer() : numeric{0}, data{0} {}
  explicit NumericDataContainer(N input_numeric) : numeric{input_numeric}, data{0} {}
  NumericDataContainer(N input_numeric, D input_data) : numeric{input_numeric}, data{input_data} {}

  template <std::convertible_to<N> T>
  std::strong_ordering operator<=>(const NumericDataContainer<T, D> &rhs) const {
    return numeric <=> N{rhs.numeric};
  }
  template <std::convertible_to<N> T>
  bool operator==(const NumericDataContainer<T, D> &rhs) const {
    return numeric == N{rhs.numeric};
  }

  template <std::convertible_to<N> T>
  std::strong_ordering operator<=>(const T &rhs) const {
    return numeric <=> N{rhs};
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
std::strong_ordering operator<=>(const NumericDataContainer<N, D> &lhs, const T &rhs) {
  return lhs.numeric <=> N{rhs};
}

template <class N, class D>
std::ostream &operator<<(std::ostream &os, const NumericDataContainer<N, D> &ndc) {
  return os << "{" << ndc.numeric << ", " << ndc.data << "}";
}

}  // namespace dlinear
