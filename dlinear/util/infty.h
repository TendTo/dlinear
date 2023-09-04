/**
 * @file infty.h
 * @author dlinear
 * @date 13 Aug 2023
 * @copyright 2023 dlinear
 * @brief Defines the infinity constant.
 */

#ifndef DLINEAR5_DLINEAR_UTIL_INFTY_H_
#define DLINEAR5_DLINEAR_UTIL_INFTY_H_

#include "dlinear/libs/gmp.h"

namespace dlinear {

extern mpq_class *mpq_class_infinity;
extern mpq_class *mpq_class_ninfinity;

void InftyStart(const mpq_t infty, const mpq_t ninfty);
void InftyStart(const mpq_class &val);
void InftyStart(double val);
void InftyFinish();

const mpq_class &mpq_infty();
const mpq_class &Infinity::Ninfty();

} // namespace dlinear

#endif //DLINEAR5_DLINEAR_UTIL_INFTY_H_
