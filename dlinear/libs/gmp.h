/**
 * @file gmp.h
 * @author tend
 * @date 09 Aug 2023
 * @copyright 2023 tend
 * GMP wrapper.
 *
 * This header includes the GMP library and provides a various helpers.
 * Other files in the library should depend on this header instead of the GMP library directly.
 * Instead of including <gmpxx.h>, include "dlinear/libs/gmp.h".
 * In the build files, instead of depending on "@linux_libs//:gmpxx", depend on "//dlinear/libs:gmp".
 */

#ifndef DLINEAR5_DLINEAR_LIBS_GMP_H_
#define DLINEAR5_DLINEAR_LIBS_GMP_H_

#include <gmpxx.h>

#include <functional>

namespace std {

template<>
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
const inline mpq_t &to_mpq_t(const mpq_class &cla) {
  return *reinterpret_cast<const mpq_t *>(cla.get_mpq_t());
}

inline mpq_t &to_mpq_t(mpq_class &cla) {
  return *reinterpret_cast<mpq_t *>(cla.get_mpq_t());
}

/**
 * Cast a mpq_t to a mpq_class.
 *
 * This works because the internal representation of a mpq_class is exactly
 * the same as that of a mpq_t (and, because we only take a reference, no
 * constructor or destructor is ever called).
 * @param mpq mpq_t to cast
 * @return mpq_class reference
 */
const inline mpq_class &to_mpq_class(const mpq_t &mpq) {
  return reinterpret_cast<const mpq_class &>(mpq);
}

/**
 * Cast a mpq_t to a mpq_class.
 *
 * This works because the internal representation of a mpq_class is exactly
 * the same as that of a mpq_t (and, because we only take a reference, no
 * constructor or destructor is ever called).
 * @param mpq mpq_t to cast
 * @return mpq_class reference
 */
inline mpq_class &to_mpq_class(mpq_t &mpq) {
  return reinterpret_cast<mpq_class &>(mpq);
}

} // namespace dlinear::gmp

#endif //DLINEAR5_DLINEAR_LIBS_GMP_H_
