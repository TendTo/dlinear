/**
 * @file qsoptex.h
 * @author tend
 * @date 10 Aug 2023
 * @copyright 2023 tend
 * @brief Qsopt_ex wrapper.
 *
 * This header includes the Qsopt_ex library and provides a various helpers.
 * Other files in the library should depend on this header instead of the Qsopt_ex library directly.
 */

#ifndef DLINEAR5_DLINEAR_LIBS_QSOPTEX_H_
#define DLINEAR5_DLINEAR_LIBS_QSOPTEX_H_

#include <gmpxx.h>

extern "C" {
#include <qsopt_ex/QSopt_ex.h>
}

namespace dlinear::qsoptex {
void printVersion();
} // namespace dlinear::qsoptex

#endif //DLINEAR5_DLINEAR_LIBS_QSOPTEX_H_
