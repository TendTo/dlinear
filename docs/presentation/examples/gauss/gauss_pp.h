#pragma once

#include "gauss.h"

namespace dlinear {

template <class T>
class GaussPP : public Gauss<T> {
 public:
  GaussPP(size_t size) : Gauss<T>(size) {}
  void forward_elimination() override;
};

}  // namespace dlinear
