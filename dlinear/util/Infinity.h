#pragma once

#include "dlinear/libs/libgmp.h"
#include "dlinear/util/Config.h"

namespace dlinear {

class Infinity {
 public:
  static const mpq_class& infinity(const Config& config);
  static const mpq_class& ninfinity(const Config& config);
  static const mpq_class& infinity(Config::LPSolver lp_solver);
  static const mpq_class& ninfinity(Config::LPSolver lp_solver);

 private:
#ifdef DLINEAR_ENABLED_QSOPTEX
  const static mpq_class qsoptex_ninfinity_;
  const static mpq_class qsoptex_infinity_;
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
  const static mpq_class soplex_ninfinity_;
  const static mpq_class soplex_infinity_;
#endif
};

}  // namespace dlinear
