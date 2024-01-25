/**
 * @file SolverGuard.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
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
