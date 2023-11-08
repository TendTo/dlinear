#include "gauss_fp.h"

#include <gmpxx.h>

#include <algorithm>
#include <stdexcept>

namespace dlinear {

template <class T>
void GaussFP<T>::forward_elimination() {
  // Full pivot forward elimination
  for (size_t i = 0; i < this->size_; ++i) {
    size_t max_row = i;
    size_t max_col = i;
    for (size_t j = i; j < this->size_; ++j) {
      for (size_t k = i; k < this->size_; ++k) {
        if (this->is_grater_than_abs(this->A_[j][k], this->A_[max_row][max_col])) {
          max_row = j;
          max_col = k;
        }
      }
    }
    std::swap(this->A_[i], this->A_[max_row]);
    std::swap(this->b_[i], this->b_[max_row]);
    if (i != max_col) {
      std::swap(this->permutation_[i], this->permutation_[max_col]);
      for (size_t j = 0; j < this->size_; ++j) {
        std::swap(this->A_[j][i], this->A_[j][max_col]);
      }
    }
    for (size_t j = i + 1; j < this->size_; ++j) {
      if (this->A_[i][i] == 0) throw std::runtime_error("Impossible system");
      if (this->A_[j][i] == 0) continue;
      T coef = this->A_[j][i] / this->A_[i][i];
      for (size_t k = i + 1; k < this->size_; ++k) {
        this->A_[j][k] -= this->A_[i][k] * coef;
      }
      this->A_[j][i] = 0.0;
      this->b_[j] -= this->b_[i] * coef;
    }
  }
}

template class GaussFP<double>;
template class GaussFP<mpq_class>;

}  // namespace dlinear
