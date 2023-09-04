/**
 * @file Infinity.h
 * @author dlinear
 * @date 04 Sep 2023
 * @copyright 2023 dlinear
 * @brief Initializes all the infinity values used as bounds in the solver.
 *
 * Singleton class that initializes all the infinity values used as bounds in
 * the solver. The infinity values are initialized in the constructor and are
 * accessible through static methods.
 */

#ifndef DLINEAR5_DLINEAR_UTIL_INFINITY_H_
#define DLINEAR5_DLINEAR_UTIL_INFINITY_H_

#include <string>

#include "dlinear/libs/gmp.h"
#include "dlinear/util/Config.h"

namespace dlinear {

class Infinity {
 private:
  static Infinity *instance_;

  Config::LPSolver lp_solver_;
  mpq_class infty_;
  mpq_class ninfty_;

  Infinity(Config::LPSolver lp_solver, mpq_class infty, mpq_class ninfty);
  ~Infinity();

  static void InftyStart(Config::LPSolver lp_solver, double value);
  static void InftyStart(Config::LPSolver lp_solver, const mpq_class &value);
  static void InftyStart(Config::LPSolver lp_solver, const mpq_t infty, const mpq_t ninfty);

 public:
  Infinity(Infinity &other) = delete;
  void operator=(const Infinity &) = delete;

  static bool IsInitialized() { return instance_ != nullptr; }
  static void InftyStart(const Config &config);
  static void InftyStart(Config::LPSolver lp_solver);
  static void InftyFinish();
  static const mpq_class &Infty();
  static const mpq_class &Ninfty();
};

}  // namespace dlinear

#endif  // DLINEAR5_DLINEAR_UTIL_INFINITY_H_
