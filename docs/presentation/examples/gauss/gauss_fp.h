#pragma once

#include "gauss.h"

namespace dlinear {

template <class T>
class GaussFP : public Gauss<T> {
 public:
  GaussFP(size_t size) : Gauss<T>(size) {}
  void forward_elimination() override;
};

}  // namespace dlinear
