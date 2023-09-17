#include "dlinear/util/Config.h"

namespace dlinear {

class SolverGuard {
 public:
  SolverGuard(const dlinear::Config &config);
  ~SolverGuard();
};

}  // namespace dlinear