/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */

#include "dlinear/util/math.h"

#include <cmath>
#include <limits>

#include "dlinear/util/error.h"
#include "dlinear/util/logging.h"

namespace dlinear {
bool IsInteger(const double v) {
  // v should be in [int_min, int_max].
  if (!((std::numeric_limits<int>::lowest() <= v) && (v <= std::numeric_limits<int>::max()))) {
    return false;
  }
  double intpart;  // dummy variable
  return std::modf(v, &intpart) == 0.0;
}

bool IsInteger(const mpq_class &v) {
  // v should be in [int_min, int_max].
  if (!((std::numeric_limits<int>::lowest() <= v) && (v <= std::numeric_limits<int>::max()))) {
    return false;
  }
  mpz_class f{v};
  return v == f;
}

int ConvertInt64ToInt(const std::int64_t v) {
  if (std::numeric_limits<int>::min() <= v && v <= std::numeric_limits<int>::max()) return static_cast<int>(v);
  DLINEAR_RUNTIME_ERROR_FMT("Fail to convert a std::int64_t value {} to int", v);
}

double ConvertInt64ToDouble(const std::int64_t v) {
  constexpr std::int64_t m{1UL << static_cast<unsigned>(std::numeric_limits<double>::digits)};
  if (-m <= v && v <= m) return static_cast<double>(v);
  DLINEAR_RUNTIME_ERROR_FMT("Fail to convert a std::int64_t value {} to double", v);
}

mpq_class ConvertInt64ToRational(std::int64_t v) { return mpq_class{v, 1}; }
}  // namespace dlinear
