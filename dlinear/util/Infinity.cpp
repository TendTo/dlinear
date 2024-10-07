/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "Infinity.h"

#include "exception.h"

#ifdef DLINEAR_ENABLED_QSOPTEX
#include "dlinear/libs/libqsopt_ex.h"
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
#include "dlinear/libs/libsoplex.h"
#endif

namespace dlinear {

bool Infinity::initialised_{false};

#ifdef DLINEAR_ENABLED_QSOPTEX
mpq_class Infinity::qsoptex_ninfinity_{0};
mpq_class Infinity::qsoptex_infinity_{0};
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
mpq_class Infinity::soplex_ninfinity_{-soplex::infinity};
mpq_class Infinity::soplex_infinity_{soplex::infinity};
#endif

const mpq_class& Infinity::infinity(const Config& config) { return infinity(config.lp_solver()); }
const mpq_class& Infinity::ninfinity(const Config& config) { return ninfinity(config.lp_solver()); }

inline void Infinity::Initialise() {
  if (initialised_) return;
#ifdef DLINEAR_ENABLED_QSOPTEX
  Infinity::qsoptex_ninfinity_ = gmp::to_mpq_class(mpq_NINFTY);
  Infinity::qsoptex_infinity_ = gmp::to_mpq_class(mpq_INFTY);
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
  Infinity::soplex_ninfinity_ = -soplex::infinity;
  Infinity::soplex_infinity_ = soplex::infinity;
#endif
  initialised_ = true;
}

const mpq_class& Infinity::infinity(const Config::LPSolver lp_solver) {
  Initialise();
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
  Initialise();
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
