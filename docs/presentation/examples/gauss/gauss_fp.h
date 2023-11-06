#pragma once

#include "gauss.h"

namespace dlinear {

template <class T>
class GaussFP : public Gauss<T> {
 public:
  GaussFP(size_t size, size_t seed = DEFAULT_SEED) : Gauss<T>(size, seed) {
    this->permutation_ = new size_t[this->size_];
    for (size_t i = 0; i < this->size_; ++i) this->permutation_[i] = i;
  }
  ~GaussFP() { delete[] this->permutation_; }
  void forward_elimination() override;
  std::string class_name() const override { return "GaussFP"; }
};

}  // namespace dlinear
