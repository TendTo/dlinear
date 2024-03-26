#pragma once

#include <iostream>
#include <type_traits>
#include <utility>

namespace dlinear {

template <class N, class D>
struct NumericDataContainer {
  using NumericType = N;
  using DataType = D;

  NumericDataContainer() : numeric{0}, data{0} {}
  explicit NumericDataContainer(N input_numeric) : numeric{input_numeric}, data{0} {}
  NumericDataContainer(N input_numeric, D input_data) : numeric{input_numeric}, data{input_data} {}

  bool operator<(const NumericDataContainer<N, D> &rhs) const { return numeric < rhs.numeric; }
  bool operator<=(const NumericDataContainer<N, D> &rhs) const { return numeric <= rhs.numeric; }
  bool operator>(const NumericDataContainer<N, D> &rhs) const { return numeric > rhs.numeric; }
  bool operator>=(const NumericDataContainer<N, D> &rhs) const { return numeric >= rhs.numeric; }
  bool operator==(const NumericDataContainer<N, D> &rhs) const { return numeric == rhs.numeric; }
  bool operator!=(const NumericDataContainer<N, D> &rhs) const { return numeric != rhs.numeric; }

  template <class T>
  bool operator<(const T &rhs) const {
    return numeric < N{rhs};
  }
  template <class T>
  bool operator<=(const T &rhs) const {
    return numeric <= N{rhs};
  }
  template <class T>
  bool operator>(const T &rhs) const {
    return numeric > N{rhs};
  }
  template <class T>
  bool operator>=(const T &rhs) const {
    return numeric >= N{rhs};
  }
  template <class T>
  bool operator==(const T &rhs) const {
    return numeric == N{rhs};
  }
  template <class T>
  bool operator!=(const T &rhs) const {
    return numeric != N{rhs};
  }

  bool EqualTo(const NumericDataContainer<N, D> &rhs) const { return numeric == rhs.numeric && data == rhs.data; }

  NumericDataContainer &operator+=(const NumericDataContainer<N, D> &rhs) {
    numeric += rhs.numeric;
    return *this;
  }
  NumericDataContainer &operator-=(const NumericDataContainer<N, D> &rhs) {
    numeric -= rhs.numeric;
    return *this;
  }
  NumericDataContainer &operator*=(const NumericDataContainer<N, D> &rhs) {
    numeric *= rhs.numeric;
    return *this;
  }
  NumericDataContainer &operator/=(const NumericDataContainer<N, D> &rhs) {
    numeric /= rhs.numeric;
    return *this;
  }

  template <class T>
  NumericDataContainer &operator+=(const T &rhs) {
    numeric += N{rhs};
    return *this;
  }
  template <class T>
  NumericDataContainer &operator-=(const T &rhs) {
    numeric -= N{rhs};
    return *this;
  }
  template <class T>
  NumericDataContainer &operator*=(const T &rhs) {
    numeric *= N{rhs};
    return *this;
  }
  template <class T>
  NumericDataContainer &operator/=(const T &rhs) {
    numeric /= N{rhs};
    return *this;
  }

  NumericDataContainer operator+(const NumericDataContainer<N, D> &rhs) const { return {numeric + rhs.numeric, data}; }
  NumericDataContainer operator-(const NumericDataContainer<N, D> &rhs) const { return {numeric - rhs.numeric, data}; }
  NumericDataContainer operator*(const NumericDataContainer<N, D> &rhs) const { return {numeric * rhs.numeric, data}; }
  NumericDataContainer operator/(const NumericDataContainer<N, D> &rhs) const { return {numeric / rhs.numeric, data}; }

  template <class T>
  NumericDataContainer operator+(const T &rhs) const {
    return {numeric + N{rhs}, data};
  }
  template <class T>
  NumericDataContainer operator-(const T &rhs) const {
    return {numeric - N{rhs}, data};
  }
  template <class T>
  NumericDataContainer operator*(const T &rhs) const {
    return {numeric * N{rhs}, data};
  }
  template <class T>
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
bool operator<(const T &lhs, const NumericDataContainer<N, D> &rhs) {
  return N{lhs} < rhs.numeric;
}
template <class N, class D, class T>
bool operator<=(const N &lhs, const NumericDataContainer<N, D> &rhs) {
  return N{lhs} <= rhs.numeric;
}
template <class N, class D, class T>
bool operator>(const N &lhs, const NumericDataContainer<N, D> &rhs) {
  return N{lhs} > rhs.numeric;
}
template <class N, class D, class T>
bool operator>=(const N &lhs, const NumericDataContainer<N, D> &rhs) {
  return N{lhs} >= rhs.numeric;
}
template <class N, class D, class T>
bool operator==(const N &lhs, const NumericDataContainer<N, D> &rhs) {
  return N{lhs} == rhs.numeric;
}
template <class N, class D, class T>
bool operator!=(const N &lhs, const NumericDataContainer<N, D> &rhs) {
  return N{lhs} != rhs.numeric;
}

template <class N, class D>
std::ostream &operator<<(std::ostream &os, const NumericDataContainer<N, D> &ndc) {
  return os << "{" << ndc.numeric << ", " << ndc.data << "}";
}

}  // namespace dlinear
