#pragma once

#include "gauss.h"

namespace dlinear {

template <class T>
class GaussNP : public Gauss<T> {
 public:
  GaussNP(size_t size, size_t seed = DEFAULT_SEED) : Gauss<T>(size, seed) {}
  void forward_elimination() override;
  std::string class_name() const override { return "GaussNP"; }
};

}  // namespace dlinear
