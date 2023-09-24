/**
 * @file SolverGuard.cpp
 * @author dlinear
 * @date 16 Sep 2023
 * @copyright 2023 dlinear
 */
#include "SolverGuard.h"

#include "dlinear/util/Infinity.h"

namespace dlinear {

SolverGuard::SolverGuard(const Config& config) { Infinity::InftyStart(config); }

SolverGuard::~SolverGuard() { DeInit(); }

void SolverGuard::DeInit() {
  if (cleared_) return;
  Infinity::InftyFinish();
  cleared_ = true;
}

}  // namespace dlinear
