#pragma once

#include "gauss.h"

namespace dlinear {

template <class T>
class GaussFP : public Gauss<T> {
 public:
  GaussFP(size_t size, size_t seed = DEFAULT_SEED) : Gauss<T>(size, seed) {}
  void forward_elimination() override;
  std::string class_name() const override { return "GaussFP"; }
};

}  // namespace dlinear
