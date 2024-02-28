/**
 * @file TestMps.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <filesystem>
#include <memory>
#include <string_view>

#include "dlinear/solver/SmtSolver.h"
#include "test/solver/TestSolverUtils.h"

using dlinear::Config;
using dlinear::get_files;
using dlinear::SmtSolver;
using dlinear::SmtSolver;
using dlinear::SolverResult;
using std::unique_ptr;

class TestMps : public ::testing::TestWithParam<std::tuple<Config::LPSolver, std::string, double>> {
 protected:
  Config config_;
};

INSTANTIATE_TEST_SUITE_P(TestMps, TestMps,
                         ::testing::Combine(enabled_test_solvers, ::testing::ValuesIn(get_files("test/solver/mps")),
                                            ::testing::Values(0.0, 0.1)));

TEST_P(TestMps, MpsInputAgainstExpectedOutput) {
//  const auto& [lp_solver, filename, precision] = GetParam();
//  config_.m_filename() = filename;
//  config_.m_lp_solver() = lp_solver;
//  config_.m_precision() = precision;
//  SmtSolver s{config_};
//  const SolverResult result = s.CheckSat().result;
//  EXPECT_THAT(expected_results(s.GetExpected()), ::testing::Contains(result));
}
