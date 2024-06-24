/**
 * @file libeigen.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Eigen wrapper.
 */
#pragma once

#include <Eigen/Core>

#include "dlinear/libs/libgmp.h"

namespace Eigen {

template <>
struct NumTraits<mpq_class> : GenericNumTraits<mpq_class> {
  typedef mpq_class Real;
  typedef mpq_class NonInteger;
  typedef mpq_class Nested;

  static Real epsilon();
  static Real dummy_precision();
  static int digits10();

  enum {
    IsInteger = 0,
    IsSigned = 1,
    IsComplex = 0,
    RequireInitialization = 1,
    ReadCost = 6,
    AddCost = 150,
    MulCost = 100
  };
};
}  // namespace Eigen
