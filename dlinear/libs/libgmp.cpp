/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @copyright cvc5 (Andrew V. Teylu, Tim King, Aina Niemetz)
 * @licence BSD 3-Clause License
 */

#include "libgmp.h"

namespace {
/**
 * Hash a gmp unsigned int.
 *
 * Credits to the [cvc5 implementation](https://github.com/cvc5/cvc5/blob/main/src/util/gmp_util.h).
 * @param val unsigned integer to hash
 * @return hash
 */
size_t gmpz_hash(const mpz_t val) {
  size_t hash = 0;
  for (int i = 0, n = mpz_size(val); i < n; ++i) {
    const mp_limb_t limb = mpz_getlimbn(val, i);
    hash = hash * 2;
    hash = hash xor limb;
  }
  return hash;
}
}  // namespace

/**
 * Hash a gmp rational.
 *
 * Credits to the [cvc5 implementation](https://github.com/cvc5/cvc5/blob/main/src/util/gmp_util.h).
 * @param val rational to hash
 * @return hash
 */
size_t std::hash<mpq_class>::operator()(const mpq_class &val) const noexcept {
  const size_t numeratorHash = gmpz_hash(val.get_num_mpz_t());
  const size_t denominatorHash = gmpz_hash(val.get_den_mpz_t());
  return numeratorHash xor denominatorHash;
}

namespace dlinear {

std::strong_ordering operator<=>(const mpq_class &lhs, const mpq_t &rhs) {
  const mpq_class &rhs_class = gmp::ToMpqClass(rhs);
  return lhs < rhs_class   ? std::strong_ordering::less
         : lhs > rhs_class ? std::strong_ordering::greater
                           : std::strong_ordering::equal;
}
std::strong_ordering operator<=>(const mpq_t &lhs, const mpq_class &rhs) {
  const mpq_class &lhs_class = gmp::ToMpqClass(lhs);
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
