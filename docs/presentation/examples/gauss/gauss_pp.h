#pragma once

#include "gauss.h"

namespace dlinear {

template <class T>
class GaussPP : public Gauss<T> {
 public:
  GaussPP(size_t size, size_t seed = DEFAULT_SEED) : Gauss<T>(size, seed) {}
  void forward_elimination() override;
  std::string class_name() const override { return "GaussPP"; }
};

}  // namespace dlinear
