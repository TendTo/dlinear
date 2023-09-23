/**
 * @file SolverGuard.h
 * @author dlinear
 * @date 16 Sep 2023
 * @copyright 2023 dlinear
 * @brief Solver guard class.
 *
 * Ensures that all the global initialization happens before the solver is
 * used.
 * When the guard is destroyed by the solver's destructor, the global state is cleaned up.
 */
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
