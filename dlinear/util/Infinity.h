/**
 * @file Infinity.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * Infinity class.
 */
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
  static void Initialise();

  static bool initialised_;
#ifdef DLINEAR_ENABLED_QSOPTEX
  static mpq_class qsoptex_ninfinity_;
  static mpq_class qsoptex_infinity_;
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
  static mpq_class soplex_ninfinity_;
  static mpq_class soplex_infinity_;
#endif
};

}  // namespace dlinear
