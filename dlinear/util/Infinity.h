/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Infinity class.
 */
#pragma once

#include "dlinear/libs/libgmp.h"
#include "dlinear/util/Config.h"

namespace dlinear {

/**
 * Global class storing the infinity values for the different LP solvers.
 *
 * The infinity values are lazily initialised when the first request is made.
 * Since different LP solvers may use different values to represent infinity,
 * they are stored separately and accessed through static methods, based on the LPSolver in the Config object.
 */
class Infinity {
 public:
  /**
   * Get the positive infinity value for the given LP solver in the @p config.
   * @param config configuration object indicating which LP solver to consider
   * @return positive infinity value
   */
  static const mpq_class& infinity(const Config& config);
  /**
   * Get the negative infinity value for the given LP solver in the @p config.
   * @param config configuration object indicating which LP solver to consider
   * @return negative infinity value
   */
  static const mpq_class& ninfinity(const Config& config);
  /**
   * Get the positive infinity value for the given @p lp_solver.
   * @param lp_solver LP solver to consider
   * @return positive infinity value
   */
  static const mpq_class& infinity(Config::LPSolver lp_solver);
  /**
   * Get the negative infinity value for the given @p lp_solver.
   * @param lp_solver LP solver to consider
   * @return negative infinity value
   */
  static const mpq_class& ninfinity(Config::LPSolver lp_solver);

 private:
  /** Lazy initialisation of the infinity values. */
  static void Initialise();

  static bool initialised_;
#ifdef DLINEAR_ENABLED_QSOPTEX
  static mpq_class qsoptex_ninfinity_;  ///< Negative infinity for QSoptEx
  static mpq_class qsoptex_infinity_;   ///< Positive infinity for QSoptEx
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
  static mpq_class soplex_ninfinity_;  ///< Negative infinity for SoPlex
  static mpq_class soplex_infinity_;   ///< Positive infinity for SoPlex
#endif
};

}  // namespace dlinear
