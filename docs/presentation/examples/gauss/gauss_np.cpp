#include "gauss_np.h"

#include <gmpxx.h>

#include <algorithm>
#include <stdexcept>

namespace dlinear {

template <class T>
void GaussNP<T>::forward_elimination() {
  // Forward elimination with no pivot
  for (size_t i = 0; i < this->size_; ++i) {
    for (size_t j = i + 1; j < this->size_; ++j) {
      if (this->A_[i][i] == 0) throw std::runtime_error("Division by zero");
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

template class GaussNP<double>;
template class GaussNP<mpq_class>;
template class GaussNP<mpf_class>;

}  // namespace dlinear
