/**
 * @file SolverGuard.cpp
 * @author dlinear
 * @date 16 Sep 2023
 * @copyright 2023 dlinear
 */
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
