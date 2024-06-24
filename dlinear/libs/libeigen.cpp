/**
 * @file libeigen.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "dlinear/libs/libeigen.h"

#include <gmpxx.h>

#include <Eigen/Core>

namespace Eigen {

NumTraits<mpq_class>::Real NumTraits<mpq_class>::epsilon() { return 0; }

NumTraits<mpq_class>::Real NumTraits<mpq_class>::dummy_precision() { return 0; }

int NumTraits<mpq_class>::digits10() { return 0; }

}  // namespace Eigen
