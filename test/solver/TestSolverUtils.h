/**
 * @file TestSolverUtils.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#pragma once

#include <gtest/gtest.h>

#include "dlinear/solver/SmtSolverOutput.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/filesystem.h"

const auto enabled_test_solvers = ::testing::Values(
#ifdef DLINEAR_ENABLED_QSOPTEX
    dlinear::Config::LPSolver::QSOPTEX,
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
    dlinear::Config::LPSolver::SOPLEX
#endif
);

std::set<dlinear::SmtResult> delta_result(dlinear::SmtResult res) {
  switch (res) {
    case dlinear::SmtResult::SAT:
      return {dlinear::SmtResult::SAT, dlinear::SmtResult::DELTA_SAT};
    case dlinear::SmtResult::DELTA_SAT:
      return {dlinear::SmtResult::DELTA_SAT};
    case dlinear::SmtResult::UNSAT:
      // return {dlinear::SmtResult::UNSAT, dlinear::SmtResult::DELTA_SAT};
      return {dlinear::SmtResult::UNSAT, dlinear::SmtResult::DELTA_SAT};
    case dlinear::SmtResult::UNKNOWN:
      return {dlinear::SmtResult::UNKNOWN};
    default:
      DLINEAR_UNREACHABLE();
  }
}