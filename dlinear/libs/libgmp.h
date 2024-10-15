/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * GMP wrapper.
 *
 * This header includes the GMP library and provides a various helpers.
 * Other files in the library should depend on this header instead of the GMP library directly.
 * Instead of including <gmpxx.h>, include "dlinear/libs/gmp.h".
 * In the build files, instead of depending on "@linux_libs//:gmpxx", depend on "//dlinear/libs:gmp".
 */
#pragma once

#include <gmp.h>    // IWYU pragma: export
#include <gmpxx.h>  // IWYU pragma: export

#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstring>
#include <string>
#include <string_view>

namespace std {

template <>
struct hash<mpq_class> {
  size_t operator()(const mpq_class &val) const;
};
}  // namespace std

namespace dlinear {

std::strong_ordering operator<=>(const mpq_class &lhs, const mpq_t &rhs);
std::strong_ordering operator<=>(const mpq_t &lhs, const mpq_class &rhs);

namespace gmp {

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
inline const mpq_t &to_mpq_t(const mpq_class &cla) { return *reinterpret_cast<const mpq_t *>(cla.get_mpq_t()); }

inline mpq_t &to_mpq_t(mpq_class &cla) { return *reinterpret_cast<mpq_t *>(cla.get_mpq_t()); }  // NOLINT

/**
 * Cast a mpq_t to a mpq_class.
 *
 * This works because the internal representation of a mpq_class is exactly
 * the same as that of a mpq_t (and, because we only take a reference, no constructor or destructor is ever called).
 * @param mpq mpq_t to cast
 * @return mpq_class reference
 */
inline const mpq_class &to_mpq_class(const mpq_t &mpq) { return reinterpret_cast<const mpq_class &>(mpq); }

/**
 * Cast a mpq_t to a mpq_class.
 *
 * This works because the internal representation of a mpq_class is exactly
 * the same as that of a mpq_t (and, because we only take a reference, no constructor or destructor is ever called).
 * @param mpq mpq_t to cast
 * @return mpq_class reference
 */
inline mpq_class &to_mpq_class(mpq_t &mpq) { return reinterpret_cast<mpq_class &>(mpq); }  // NOLINT

/**
 * Check if the char is either a digit or a plus/minus sign.
 * @param c The char to check
 * @return true if the char is a digit or a plus/minus sign
 * @return false if the char is not a digit or a plus/minus sign
 */
inline bool is_digit_or_sign(char c) { return std::isdigit(c) || c == '+' || c == '-'; }

/**
 * Convert a string to a mpq_class.
 *
 * The number is converted exactly, without any rounding,
 * by interpreting the string as a base-10 rational number.
 * @code
 * string_to_mpq("0") == 0
 * string_to_mpq(".") == 0
 * string_to_mpq("0.") == 0
 * string_to_mpq(".0") == 0
 * string_to_mpq("15") == 15/1
 * string_to_mpq("1.5") == 15/10
 * string_to_mpq("15.") == 15/1
 * string_to_mpq(".15") == 15/100
 * string_to_mpq("15.0") == 15/1
 * string_to_mpq("15.00") == 15/1
 * string_to_mpq("15") == 15/1
 * string_to_mpq("1.5E2") == 15/10 * 10^2
 * string_to_mpq("1.5E-2") == 15/10 * 10^-2
 * string_to_mpq("E+2") == 1/1 * 10^2
 * string_to_mpq("15/6") == 15/6
 * string_to_mpq("0/1010") == 0
 * string_to_mpq("inf") == 1e100
 * string_to_mpq("-inf") == -1e100
 * @endcode
 * @note Only a single leading + or - sign is allowed.
 * @warning If the string is not a valid rational number, the result is undefined.
 * @param str The string to convert.
 * @return The mpq_class instance.
 */
inline mpq_class string_to_mpq(std::string_view str) {
  // Remove leading + and - sign
  const bool is_negative = str[0] == '-';
  if (is_negative || str[0] == '+') str.remove_prefix(1);
  if (str == "inf") return {1e100};
  if (str == "-inf") return {-1e100};

  // case 1: string is given in integer format
  const size_t symbol_pos = str.find_first_of("/.Ee");
  if (symbol_pos == std::string::npos) {
    const size_t start_pos = str.find_first_not_of('0', str[0] == '+' ? 1 : 0);
    if (start_pos == std::string_view::npos) return {0};
    //    DLINEAR_ASSERT_FMT(std::all_of(str.cbegin() + start_pos, str.cend(), is_digit_or_sign), "Invalid number: {}",
    //    str);
    return is_negative ? -mpq_class{str.data() + start_pos} : mpq_class{str.data() + start_pos};
  }

  // case 2: string is given in nom/denom format
  if (str[symbol_pos] == '/') {
    mpq_class res{str.data()};
    res.canonicalize();
    return is_negative ? -res : res;
  }

  const size_t e_pos = str[symbol_pos] == 'e' || str[symbol_pos] == 'E' ? symbol_pos : str.find_first_of("Ee");
  mpz_class mult{is_negative ? -1 : 1};
  bool is_exp_positive = true;

  // case 3a: string is given as base-10 decimal number (e)
  if (e_pos != std::string::npos) {
    const long exponent = std::stol(str.data() + e_pos + 1);  // NOLINT(runtime/int)
    is_exp_positive = exponent >= 0;
    mult = 10;
    mpz_pow_ui(mult.get_mpz_t(), mult.get_mpz_t(), std::abs(exponent));
    if (is_negative) mult = -mult;
    // Remove the exponent
    str = str.substr(0, e_pos);

    if (str.empty()) return is_exp_positive ? mpq_class{mult} : is_negative ? mpq_class{-1, -mult} : mpq_class{1, mult};
  }

  const size_t &len = str.length();

  // case 3b: string does not contain a . , only an exponent E
  if (str[symbol_pos] == 'e' || str[symbol_pos] == 'E') {
    int plus_pos = str[0] == '+' ? 1 : 0;
    //    DLINEAR_ASSERT_FMT(std::all_of(str.cbegin() + plus_pos, str.cend(), is_digit_or_sign), "Invalid number: {}",
    //    str);

    char *const str_number = new char[len - plus_pos + 1];
    memcpy(str_number, str.data() + plus_pos, len - plus_pos);
    str_number[len - plus_pos] = '\0';
    mpq_class res{str_number, 10};
    delete[] str_number;
    return res * mult;
  }

  const size_t &dot_pos = symbol_pos;

  // case 3c: string contains a .
  size_t start_pos = str.find_first_not_of('0');
  size_t digits;

  // case 4a: string starts with a . or the numbers before the . are all 0
  if (start_pos == dot_pos) {
    start_pos = str.find_first_not_of('0', dot_pos + 1);
    // case 5: string contains only a .
    if (start_pos == std::string_view::npos) {
      return {0};
    } else {
      digits = len - start_pos;
    }
  } else {  // case 4b: string does not start with a . and the numbers before the . are not all 0
    digits = len - start_pos - 1;
  }

  const size_t n_decimals = len - dot_pos - 1;
  //  DLINEAR_ASSERT_FMT(std::all_of(str.begin() + start_pos, str.begin() + dot_pos, is_digit_or_sign),
  //                     "Invalid number: {}", str);
  //  DLINEAR_ASSERT_FMT(std::all_of(str.begin() + dot_pos + 1, str.cend(), is_digit_or_sign), "Invalid number: {}",
  //  str);
  char *const str_number = new char[digits + n_decimals + 3];

  if (digits > n_decimals) {
    memcpy(str_number, str.data() + start_pos, digits - n_decimals);
    memcpy(str_number + dot_pos, str.data() + dot_pos + 1, n_decimals);
  } else {
    memcpy(str_number, str.data() + start_pos, n_decimals);
  }

  str_number[digits] = '/';
  str_number[digits + 1] = '1';
  memset(str_number + digits + 2, '0', n_decimals);
  str_number[digits + 2 + n_decimals] = '\0';

  mpq_class res{str_number, 10};
  delete[] str_number;
  res.canonicalize();
  return is_exp_positive ? mpq_class{res * mult} : res / mult;
}

}  // namespace gmp

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(mpq_class)

#endif
