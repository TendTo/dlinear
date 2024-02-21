/**
 * @file SolverGuard.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Solver guard class.
 *
 * Ensures that all the global initialization happens before the solver is
 * used.
 * When the guard is destroyed by the solver's destructor, the global state is cleaned up.
 */
#pragma once

#include "dlinear/util/Config.h"

namespace dlinear {

class SolverGuard {
 public:
  explicit SolverGuard(const dlinear::Config &config);
  ~SolverGuard();

  void DeInit();

 private:
  bool cleared_{false};
};

}  // namespace dlinear
