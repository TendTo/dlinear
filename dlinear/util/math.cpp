/**
 * @file math.cpp
 * @author dlinear
 * @date 14 Aug 2023
 * @copyright 2023 dlinear
 */

#include "dlinear/util/math.h"

#include <cmath>
#include <iostream>
#include <limits>

#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {
bool is_integer(const double v) {
  // v should be in [int_min, int_max].
  if (!((std::numeric_limits<int>::lowest() <= v) && (v <= std::numeric_limits<int>::max()))) {
    return false;
  }
  double intpart;  // dummy variable
  return modf(v, &intpart) == 0.0;
}

bool is_integer(const mpq_class &v) {
  // v should be in [int_min, int_max].
  if (!((std::numeric_limits<int>::lowest() <= v) && (v <= std::numeric_limits<int>::max()))) {
    return false;
  }
  mpz_class f{v};
  return v == f;
}

int convert_int64_to_int(const std::int64_t v) {
  if (std::numeric_limits<int>::min() <= v && v <= std::numeric_limits<int>::max()) return static_cast<int>(v);
  DLINEAR_RUNTIME_ERROR_FMT("Fail to convert a std::int64_t value {} to int", v);
}

double convert_int64_to_double(const std::int64_t v) {
  constexpr std::int64_t m{1UL << static_cast<unsigned>(std::numeric_limits<double>::digits)};
  if (-m <= v && v <= m) return static_cast<double>(v);
  DLINEAR_RUNTIME_ERROR_FMT("Fail to convert a std::int64_t value {} to double", v);
}

mpq_class convert_int64_to_rational(const std::int64_t v) {
  DLINEAR_TRACE_FMT("convert_int64_to_rational({})", v);
  return mpq_class{v, 1};
}
}  // namespace dlinear
