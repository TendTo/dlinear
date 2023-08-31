/**
 * @file infty.cpp
 * @author dlinear
 * @date 13 Aug 2023
 * @copyright 2023 dlinear
 */

#include "infty.h"

#include "dlinear/util/logging.h"

namespace dlinear {

mpq_class *mpq_class_infinity = nullptr;
mpq_class *mpq_class_ninfinity = nullptr;

void InftyStart(double val) {
  DLINEAR_TRACE_FMT("InftyStart({})", val);
  mpq_class_infinity = new mpq_class(val);
  mpq_class_ninfinity = new mpq_class(-val);
}

void InftyStart(const mpq_class &val) {
  DLINEAR_TRACE_FMT("InftyStart({})", val.get_d());
  mpq_class_infinity = new mpq_class(val);
  mpq_class_ninfinity = new mpq_class(-val);
}

void InftyStart(const mpq_t infty, const mpq_t ninfty) {
  DLINEAR_TRACE_FMT("InftyStart({}, {})", mpq_get_d(infty), mpq_get_d(ninfty));
  mpq_class_infinity = new mpq_class(infty);
  mpq_class_ninfinity = new mpq_class(ninfty);
}

void InftyFinish() {
  DLINEAR_TRACE("InftyFinish()");
  delete mpq_class_infinity;
  delete mpq_class_ninfinity;
}

// Important: must call InftyStart() first!
// Also, if using QSXStart(), must call it before InftyStart().

const mpq_class &mpq_infty() {
  return *mpq_class_infinity;
}

const mpq_class &mpq_ninfty() {
  return *mpq_class_ninfinity;
}

} // namespace dlinear
