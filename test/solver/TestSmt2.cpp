/**
 * @file TestSmt2.cpp
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
using dlinear::SolverResult;
using std::unique_ptr;

class TestDeltaSmt2 : public ::testing::TestWithParam<std::tuple<Config::LPSolver, std::string, double>> {
 protected:
  Config config_;

  void SetUp() override { config_.m_format() = Config::Format::SMT2; }
};

class TestCompleteSmt2 : public ::testing::TestWithParam<std::tuple<Config::LPSolver, std::string>> {
 protected:
  Config config_;

  void SetUp() override {
    config_.m_precision() = 0.0;
    config_.m_complete() = true;
    config_.m_format() = Config::Format::SMT2;
  }
};

INSTANTIATE_TEST_SUITE_P(TestSmt2, TestDeltaSmt2,
                         ::testing::Combine(enabled_test_solvers, ::testing::ValuesIn(get_files("test/solver/smt2")),
                                            ::testing::Values(0.0, 0.1)));

INSTANTIATE_TEST_SUITE_P(TestSmt2, TestCompleteSmt2,
                         ::testing::Combine(enabled_test_solvers, ::testing::ValuesIn(get_files("test/solver/smt2"))));

TEST_P(TestDeltaSmt2, Smt2InputAgainstExpectedOutput) {
  const auto& [lp_solver, filename, precision] = GetParam();
  std::cout << "Testing " << filename << std::endl;
  config_.m_filename() = filename;
  config_.m_lp_solver() = lp_solver;
  config_.m_precision() = precision;
  SmtSolver s{config_};
  const SolverResult result = s.CheckSat().result;
  EXPECT_THAT(expected_results(s.GetExpected()), ::testing::Contains(result));
}

TEST_P(TestCompleteSmt2, Smt2InputAgainstExpectedOutput) {
  const auto& [lp_solver, filename] = GetParam();
  config_.m_filename() = filename;
  config_.m_lp_solver() = lp_solver;
  SmtSolver s{config_};
  const SolverResult result = s.CheckSat().result;
  EXPECT_EQ(s.GetExpected(), result);
}
