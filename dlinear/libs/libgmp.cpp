/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */

#include "libgmp.h"

namespace std {

// https://en.cppreference.com/w/cpp/utility/hash/operator()
size_t hash<mpq_class>::operator()(const mpq_class &val) const {
  mp_limb_t result = 2166136261;
  size_t num_size = mpz_size(val.get_num_mpz_t());
  size_t den_size = mpz_size(val.get_den_mpz_t());
  const mp_limb_t *num_limbs = mpz_limbs_read(val.get_num_mpz_t());
  const mp_limb_t *den_limbs = mpz_limbs_read(val.get_den_mpz_t());
  for (size_t i = 0; i < num_size; i++) {
    result = (result * 16777619) ^ num_limbs[i];
  }
  for (size_t i = 0; i < den_size; i++) {
    result = (result * 16777619) ^ den_limbs[i];
  }
  return static_cast<size_t>(result);
}

}  // namespace std

namespace dlinear {

std::strong_ordering operator<=>(const mpq_class &lhs, const mpq_t &rhs) {
  const mpq_class &rhs_class = gmp::to_mpq_class(rhs);
  return lhs < rhs_class   ? std::strong_ordering::less
         : lhs > rhs_class ? std::strong_ordering::greater
                           : std::strong_ordering::equal;
}
std::strong_ordering operator<=>(const mpq_t &lhs, const mpq_class &rhs) {
  const mpq_class &lhs_class = gmp::to_mpq_class(lhs);
  return lhs_class < rhs   ? std::strong_ordering::less
         : lhs_class > rhs ? std::strong_ordering::greater
                           : std::strong_ordering::equal;
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
