#pragma once

#include <gtest/gtest.h>

#include "dlinear/util/Config.h"

const auto enabled_test_solvers = ::testing::Values(
#ifdef DLINEAR_ENABLED_QSOPTEX
    dlinear::Config::LPSolver::QSOPTEX,
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
    dlinear::Config::LPSolver::SOPLEX
#endif
);
