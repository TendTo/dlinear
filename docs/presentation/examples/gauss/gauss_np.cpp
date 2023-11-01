#include "gauss_np.h"

#include <gmpxx.h>

#include <algorithm>
#include <stdexcept>

namespace dlinear {

template <>
void GaussNP<double>::forward_elimination() {
  // Forward elimination with no pivot
  for (size_t i = 0; i < size_; ++i) {
    for (size_t j = i + 1; j < size_; ++j) {
      if (A_[i][i] == 0) throw std::runtime_error("Division by zero");
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
void GaussNP<mpq_class>::forward_elimination() {
  for (size_t i = 0; i < size_; ++i) {
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
