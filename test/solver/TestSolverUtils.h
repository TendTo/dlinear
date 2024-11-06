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
