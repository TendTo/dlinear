#include "gauss_pp.h"

#include <gmpxx.h>

#include <algorithm>
#include <iostream>
#include <stdexcept>

namespace dlinear {

template <class T>
void GaussPP<T>::forward_elimination() {
  // Partial pivoting
  for (size_t i = 0; i < this->size_; ++i) {
    size_t max_row = i;
    for (size_t j = i + 1; j < this->size_; ++j) {
      if (this->is_grater_than_abs(this->A_[j][i], this->A_[max_row][i])) {
        max_row = j;
      }
    }
    std::swap(this->A_[i], this->A_[max_row]);
    std::swap(this->b_[i], this->b_[max_row]);
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

template class GaussPP<double>;
template class GaussPP<mpq_class>;
template class GaussPP<mpf_class>;

}  // namespace dlinear
