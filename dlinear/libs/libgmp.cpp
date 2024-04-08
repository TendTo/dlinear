/**
 * @file gmp.cpp
 * @author dlinear
 * @date 09 Aug 2023
 * @copyright 2023 dlinear
 */

#include "libgmp.h"

namespace dlinear {

void hash_append(InvocableHashAlgorithm auto &hasher, const mpq_class &val) noexcept {
  mp_limb_t result = 2166136261;
  const size_t num_size = mpz_size(val.get_num_mpz_t());
  const size_t den_size = mpz_size(val.get_den_mpz_t());
  const mp_limb_t *num_limbs = mpz_limbs_read(val.get_num_mpz_t());
  const mp_limb_t *den_limbs = mpz_limbs_read(val.get_den_mpz_t());
  for (size_t i = 0; i < num_size; i++) result = (result * 16777619) ^ num_limbs[i];
  for (size_t i = 0; i < den_size; i++) result = (result * 16777619) ^ den_limbs[i];
  hasher(static_cast<size_t>(result), sizeof(size_t));
}

namespace gmp {

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

}  // namespace gmp

}  // namespace dlinear
