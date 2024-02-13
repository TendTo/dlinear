/**
 * @file TestSolver.cpp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 */

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <filesystem>
#include <memory>
#include <string_view>

#include "dlinear/solver/Solver.h"
#include "test/solver/TestSolverUtils.h"

using dlinear::Config;
using dlinear::get_files;
using dlinear::Solver;
using dlinear::SolverOutput;
using dlinear::SolverResult;
using std::unique_ptr;

class TestSmt2 : public ::testing::TestWithParam<std::tuple<Config::LPSolver, std::string, double>> {
 protected:
  Config config_;
};

INSTANTIATE_TEST_SUITE_P(TestSmt2, TestSmt2,
                         ::testing::Combine(enabled_test_solvers, ::testing::ValuesIn(get_files("test/solver/smt2")),
                                            ::testing::Values(0.0, 0.1)));

TEST_P(TestSmt2, Smt2InputAgainstExpectedOutput) {
  const auto& [lp_solver, filename, precision] = GetParam();
  config_.m_filename() = filename;
  config_.m_lp_solver() = lp_solver;
  config_.m_precision() = precision;
  Solver s{config_};
  const SolverResult result = s.CheckSat().result();
  EXPECT_THAT(expected_results(s.GetExpected()), ::testing::Contains(result));
}
