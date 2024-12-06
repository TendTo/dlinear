/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Eigen wrapper.
 *
 * This header includes the eigen library and provides a various helpers.
 * Other files in the library should depend on this header instead of the GMP library directly.
 * Instead of including <eigen.h>, include "dlinear/libs/eigen.h".
 */
#pragma once

#include <gmpxx.h>

#include <Eigen/Core>
#include <Eigen/Sparse>

namespace Eigen {
template <>
struct NumTraits<mpq_class> : GenericNumTraits<mpq_class> {
  typedef mpq_class Real;
  typedef mpq_class NonInteger;
  typedef mpq_class Nested;

  static inline Real epsilon() { return 0; }
  static inline Real dummy_precision() { return 0; }
  static inline int digits10() { return 0; }

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

namespace internal {
#if 0
template <>
struct scalar_score_coeff_op<mpq_class> {
  struct result_type {
    std::size_t len;
    explicit result_type(const int i = 0) : len(i) {}  // Eigen uses Score(0) and Score()
    explicit result_type(const mpq_class& q) : len(mpz_size(q.get_num_mpz_t()) + mpz_size(q.get_den_mpz_t()) - 1) {}
    std::strong_ordering operator<=>(const result_type& y) const {
      if (len == y.len) return std::strong_ordering::equal;
      return (len < y.len) ? std::strong_ordering::less : std::strong_ordering::greater;
    }
  };
  result_type operator()(const mpq_class& x) const { return result_type{x}; }
};
#endif
}  // namespace internal
}  // namespace Eigen
