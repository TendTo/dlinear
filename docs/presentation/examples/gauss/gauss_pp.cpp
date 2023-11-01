#include "gauss_pp.h"

#include <gmpxx.h>

#include <algorithm>
#include <iostream>
#include <stdexcept>

namespace dlinear {

namespace {

bool is_grater_than_abs(const mpq_class& a, const mpq_class& b) {
  if (a > 0 && b > 0) {
    return a > b;
  } else if (a < 0 && b < 0) {
    return a < b;
  } else if (a >= 0) {
    return true;
  } else {
    return false;
  }
}

}  // namespace

template <>
void GaussPP<double>::forward_elimination() {
  // Partial pivoting
  for (size_t i = 0; i < size_; ++i) {
    size_t max_row = i;
    for (size_t j = i + 1; j < size_; ++j) {
      if (std::abs(A_[j][i]) > std::abs(A_[max_row][i])) {
        max_row = j;
      }
    }
    std::swap(A_[i], A_[max_row]);
    std::swap(b_[i], b_[max_row]);
    for (size_t j = i + 1; j < size_; ++j) {
      if (A_[i][i] == 0) throw std::runtime_error("Impossible system");
      if (A_[j][i] == 0) continue;
      double coef = A_[j][i] / A_[i][i];
      for (size_t k = i + 1; k < size_; ++k) {
        A_[j][k] -= A_[i][k] * coef;
      }
      A_[j][i] = 0.0;
      b_[j] -= b_[i] * coef;
    }
  }
}

template <>
void GaussPP<mpq_class>::forward_elimination() {
  // Partial pivoting
  for (size_t i = 0; i < size_; ++i) {
    size_t max_row = i;
    for (size_t j = i + 1; j < size_; ++j) {
      if (is_grater_than_abs(A_[j][i], A_[max_row][i])) {
        max_row = j;
      }
    }
    std::swap(A_[i], A_[max_row]);
    std::swap(b_[i], b_[max_row]);
    for (size_t j = i + 1; j < size_; ++j) {
      if (A_[i][i] == 0) throw std::runtime_error("Impossible system");
      if (A_[j][i] == 0) continue;
      mpq_class coef = A_[j][i] / A_[i][i];
      for (size_t k = i + 1; k < size_; ++k) {
        A_[j][k] -= A_[i][k] * coef;
      }
      A_[j][i] = 0.0;
      b_[j] -= b_[i] * coef;
    }
  }
}

}  // namespace dlinear
