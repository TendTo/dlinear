/**
 * @file gmp.h
 * @author dlinear
 * @date 09 Aug 2023
 * @copyright 2023 dlinear
 * GMP wrapper.
 *
 * This header includes the GMP library and provides a various helpers.
 * Other files in the library should depend on this header instead of the GMP library directly.
 * Instead of including <gmpxx.h>, include "dlinear/libs/gmp.h".
 * In the build files, instead of depending on "@linux_libs//:gmpxx", depend on "//dlinear/libs:gmp".
 */
#pragma once

#include <gmpxx.h>

#include <cassert>
#include <cmath>

namespace std {

template <>
struct hash<mpq_class> {
  size_t operator()(const mpq_class &val) const;
};

}  // namespace std

namespace dlinear::gmp {

/**
 * Calculate the floor of a rational number.
 * @param val The rational number.
 * @return The floor of the rational number.
 */
mpz_class floor(const mpq_class &val);
/**
 * Calculate the ceil of a rational number.
 * @param val The rational number.
 * @return The ceil of the rational number.
 */
mpz_class ceil(const mpq_class &val);

/**
 * Cast a mpq_class to a mpq_t.
 *
 * Important definitions from <gmpxx.h> and <gmp.h> (fair use):
 *
 *   mpq_srcptr mpq_class::get_mpq_t() const { return mp; }
 *   mpq_ptr mpq_class::get_mpq_t() { return mp; }
 *
 *   typedef const __mpq_struct *mpq_srcptr;
 *   typedef __mpq_struct *mpq_ptr;
 *   typedef __mpq_struct mpq_t[1];
 *
 * We can cast mpq_ptr to mpq_t * (or mpq_srcptr to const mpq_t *).
 * This is the same as casting (__mpq_struct *) to (__mpq_struct (*)[1]).
 * It's okay because it converts a pointer to a struct, to a pointer to an
 * array of that struct (which is always okay).
 *
 * We can then dereference the (mpq_t *) to obtain a mpq_t.
 * Because mpq_t is an array type, it is still effectively treated as a pointer
 * in certain contexts (such as when returning it from / passing it into a
 * function).
 * This pointer has the same value as the (mpq_t *).
 *
 * We can then take a reference to the mpq_t.
 * The address of this reference also has the same value as the (mpq_t *).
 *
 * @param cla mpq_class to cast
 * @return mpq_t reference
 */
const inline mpq_t &to_mpq_t(const mpq_class &cla) { return *reinterpret_cast<const mpq_t *>(cla.get_mpq_t()); }

inline mpq_t &to_mpq_t(mpq_class &cla) { return *reinterpret_cast<mpq_t *>(cla.get_mpq_t()); }  // NOLINT

/**
 * Cast a mpq_t to a mpq_class.
 *
 * This works because the internal representation of a mpq_class is exactly
 * the same as that of a mpq_t (and, because we only take a reference, no
 * constructor or destructor is ever called).
 * @param mpq mpq_t to cast
 * @return mpq_class reference
 */
const inline mpq_class &to_mpq_class(const mpq_t &mpq) { return reinterpret_cast<const mpq_class &>(mpq); }

/**
 * Cast a mpq_t to a mpq_class.
 *
 * This works because the internal representation of a mpq_class is exactly
 * the same as that of a mpq_t (and, because we only take a reference, no
 * constructor or destructor is ever called).
 * @param mpq mpq_t to cast
 * @return mpq_class reference
 */
inline mpq_class &to_mpq_class(mpq_t &mpq) { return reinterpret_cast<mpq_class &>(mpq); }  // NOLINT

static constexpr long pow_10(size_t n) {
  constexpr long powers_of_10[] = {1,
                                   10,
                                   100,
                                   1000,
                                   10000,
                                   100000,
                                   1000000,
                                   10000000,
                                   100000000,
                                   1000000000,
                                   100000000,
                                   10000000000,
                                   100000000000,
                                   1000000000000,
                                   10000000000000,
                                   100000000000000,
                                   1000000000000000,
                                   10000000000000000,
                                   100000000000000000,
                                   1000000000000000000};
  return powers_of_10[n];
}

inline mpq_class mpq_from_string(const char *desc) {
  if (0 == strcmp(desc, "inf")) return 1e100;
  if (0 == strcmp(desc, "-inf")) return -1e100;

  std::string_view s{desc};

  /* case 1: string is given in nom/decimal format */
  if (s.find_first_of(".Ee") == std::string::npos) {
    return s[0] == '+' ? mpq_class(s.substr(1).data()) : mpq_class(s.data());
  }

  /* case 2: string is given as base-10 decimal number */
  size_t e_pos = s.find_first_of("Ee");
  long mult = 0, numerator = 0, decimal = 1;

  if (e_pos != std::string::npos) {
    mult = std::stol(s.substr(e_pos + 1, s.length()).data());
    // Remove the exponent
    s = s.substr(0, e_pos);
  }

  /* case 3a: string starts with a . */
  // if (s[0] == '.') s.insert(0, "0");
  size_t dot_pos = s.find('.');

  // if s contains a ., convert it to a rational
  switch (dot_pos) {
    case 0:
      assert(std::all_of(s.cbegin() + 1, s.cend(), ::isdigit));
      numerator = 0;
      decimal = std::stol(s.substr(1, s.length()).data());
      break;
    case std::string::npos:
      assert(std::all_of(s.cbegin(), s.cend(), ::isdigit));
      numerator = std::stol(s.data());
      dot_pos = s.length() + 1;
      decimal = 0;
      break;
    default:
      assert(std::all_of(s.cbegin(), s.cend() + dot_pos, ::isdigit));
      assert(std::all_of(s.cbegin() + dot_pos + 1, s.cend(), ::isdigit));
      numerator = std::stol(s.substr(0, dot_pos).data());
      decimal = std::stol(s.substr(dot_pos + 1, s.length()).data());
  }

  size_t n_decimals = s.length() - dot_pos - 1;
  numerator *= pow_10(n_decimals);
  numerator += decimal;

  mpq_class res(numerator, mpz_class(pow_10(n_decimals)));
  res *= pow_10(mult);
  return res;
}

}  // namespace dlinear::gmp
