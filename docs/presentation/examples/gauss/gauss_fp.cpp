#include "gauss_fp.h"

#include <gmpxx.h>

#include <algorithm>
#include <stdexcept>

namespace dlinear {

namespace {

bool is_grater_than_abs(const mpq_class& a, const mpq_class& b) {
  if (sgn(a) > 0 && sgn(b) > 0) {
    return a > b;
  } else if (sgn(a) < 0 && sgn(b) < 0) {
    return a < b;
  } else if (sgn(a) >= 0) {
    return true;
  } else {
    return false;
  }
}

}  // namespace

template <>
void GaussFP<double>::forward_elimination() {
  // Full pivot forward elimination
  for (size_t i = 0; i < size_; ++i) {
    size_t max_row = i;
    size_t max_col = i;
    for (size_t j = i; j < size_; ++j) {
      for (size_t k = i; k < size_; ++k) {
        if (std::abs(A_[j][k]) > std::abs(A_[max_row][max_col])) {
          max_row = j;
          max_col = k;
        }
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
void GaussFP<mpq_class>::forward_elimination() {
  // Full pivot forward elimination
  for (size_t i = 0; i < size_; ++i) {
    size_t max_row = i;
    size_t max_col = i;
    for (size_t j = i; j < size_; ++j) {
      for (size_t k = i; k < size_; ++k) {
        if (is_grater_than_abs(A_[j][k], A_[max_row][max_col])) {
          max_row = j;
          max_col = k;
        }
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
