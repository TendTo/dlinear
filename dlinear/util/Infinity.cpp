#include "Infinity.h"

#include "exception.h"

#ifdef DLINEAR_ENABLED_QSOPTEX
#include "dlinear/libs/libqsopt_ex.h"
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
#include "dlinear/libs/libsoplex.h"
#endif

namespace dlinear {

#ifdef DLINEAR_ENABLED_QSOPTEX
const mpq_class Infinity::qsoptex_ninfinity_{mpq_NINFTY};
const mpq_class Infinity::qsoptex_infinity_{mpq_INFTY};
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
const mpq_class Infinity::soplex_ninfinity_{-soplex::infinity};
const mpq_class Infinity::soplex_infinity_{soplex::infinity};
#endif

const mpq_class& Infinity::infinity(const Config& config) { return infinity(config.lp_solver()); }
const mpq_class& Infinity::ninfinity(const Config& config) { return ninfinity(config.lp_solver()); }

const mpq_class& Infinity::infinity(const Config::LPSolver lp_solver) {
  switch (lp_solver) {
#ifdef DLINEAR_ENABLED_QSOPTEX
    case Config::LPSolver::QSOPTEX:
      return qsoptex_infinity_;
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
    case Config::LPSolver::SOPLEX:
      return soplex_infinity_;
#endif
    default:
      DLINEAR_UNREACHABLE();
  }
}

const mpq_class& Infinity::ninfinity(const Config::LPSolver lp_solver) {
  switch (lp_solver) {
#ifdef DLINEAR_ENABLED_QSOPTEX
    case Config::LPSolver::QSOPTEX:
      return qsoptex_ninfinity_;
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
    case Config::LPSolver::SOPLEX:
      return soplex_ninfinity_;
#endif
    default:
      DLINEAR_UNREACHABLE();
  }
}

}  // namespace dlinear