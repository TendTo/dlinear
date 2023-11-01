#pragma once

#include "gauss.h"

namespace dlinear {

template <class T>
class GaussNP : public Gauss<T> {
 public:
  GaussNP(size_t size) : Gauss<T>(size) {}
  void forward_elimination() override;
};

}  // namespace dlinear
