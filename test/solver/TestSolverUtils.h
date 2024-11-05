/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Solvers utilities for testing.
 */
#pragma once

#include <gtest/gtest.h>

#include "dlinear/solver/SmtSolverOutput.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/error.h"
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
      return {dlinear::SmtResult::UNSAT, dlinear::SmtResult::DELTA_SAT};
    default:
      DLINEAR_UNREACHABLE();
  }
}

bool delta_match_expected(const dlinear::SmtSolverOutput& output, dlinear::SmtResult expected) {
  switch (expected) {
    case dlinear::SmtResult::SAT:
    case dlinear::SmtResult::DELTA_SAT:
      return output.is_sat();
    case dlinear::SmtResult::UNSAT:
      return true;
    default:
      DLINEAR_UNREACHABLE();
  }
}