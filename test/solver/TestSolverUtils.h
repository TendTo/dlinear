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

std::vector<dlinear::SolverResult> expected_results(dlinear::SolverResult res) {
  switch (res) {
    case dlinear::SolverResult::SAT:
      return std::vector{dlinear::SolverResult::SAT, dlinear::SolverResult::DELTA_SAT};
    case dlinear::SolverResult::DELTA_SAT:
      return std::vector{dlinear::SolverResult::DELTA_SAT};
    case dlinear::SolverResult::UNSAT:
      // return std::vector{dlinear::SolverResult::UNSAT, dlinear::SolverResult::DELTA_SAT};
      return std::vector{dlinear::SolverResult::UNSAT, dlinear::SolverResult::DELTA_SAT};
    case dlinear::SolverResult::UNKNOWN:
      return std::vector{dlinear::SolverResult::UNKNOWN};
    default:
      DLINEAR_UNREACHABLE();
  }
}