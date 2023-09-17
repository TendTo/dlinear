#include "SolverGuard.h"

#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Infinity.h"

namespace dlinear {

SolverGuard::SolverGuard(const Config& config) {
  Infinity::InftyStart(config);
  Expression::InitConstants();
}

SolverGuard::~SolverGuard() {
  Expression::DeInitConstants();
  Infinity::InftyFinish();
}

}  // namespace dlinear
