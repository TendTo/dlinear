/**
 * @file gmp.cpp
 * @author tend
 * @date 09 Aug 2023
 * @copyright 2023 tend
 */
#include "gmp.h"

namespace dlinear::gmp {

mpz_class floor(const mpq_class &val) {
  // This rounds towards zero
  mpz_class t{val};
  if (t == val || val > 0) {
    return t;
  } else {
    // val is negative and non-integer, so it was rounded upwards
    return t - 1;
  }
}

mpz_class ceil(const mpq_class &val) {
  // This rounds towards zero
  mpz_class t{val};
  if (t == val || val < 0) {
    return t;
  } else {
    // val is positive and non-integer, so it was rounded downwards
    return t + 1;
  }
}

mpz_class add(const mpz_class &a, const mpz_class &b) {
  return a + b;
}

} // namespace dlinear::gmp
