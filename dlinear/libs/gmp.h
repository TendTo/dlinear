/**
 * @file gmp.h
 * @author tend
 * @date 09 Aug 2023
 * @copyright 2023 tend
 * @brief GMP wrapper.
 *
 * This header includes the GMP library and provides a various helpers.
 * Other files in the library should depend on this header instead of the GMP library directly.
 */

#ifndef DLINEAR5_DLINEAR_LIBS_GMP_H_
#define DLINEAR5_DLINEAR_LIBS_GMP_H_

#include <gmpxx.h>

namespace dlinear::gmp {

mpz_class floor(const mpq_class &val);
mpz_class ceil(const mpq_class &val);
mpz_class add(const mpz_class &a, const mpz_class &b);

} // namespace dlinear::gmp

#endif //DLINEAR5_DLINEAR_LIBS_GMP_H_
