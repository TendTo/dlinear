/**
 * @file TestCompleteSmt2.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <filesystem>
#include <string_view>

#include "dlinear/solver/SmtSolver.h"
#include "test/solver/TestSolverUtils.h"

using dlinear::Config;
using dlinear::get_files;
using dlinear::SmtResult;
using dlinear::SmtSolver;

class TestCompleteSmt2 : public ::testing::TestWithParam<
                             std::tuple<Config::LPSolver, std::string, Config::PreprocessingRunningFrequency>> {
 protected:
  Config config_;

  TestCompleteSmt2() {
    const auto& [lp_solver, filename, frequency] = GetParam();
    config_.m_precision() = 0.0;
    config_.m_complete() = true;
    config_.m_format() = Config::Format::SMT2;
    config_.m_filename() = filename;
    config_.m_lp_solver() = lp_solver;
    config_.m_bound_propagation_type() = Config::BoundPropagationType::AUTO;
    config_.m_bound_propagation_frequency() = frequency;
    config_.m_bound_implication_frequency() = frequency;
    std::cout << "Testing " << filename << std::endl;
  }
};

INSTANTIATE_TEST_SUITE_P(TestCompleteSmt2, TestCompleteSmt2,
                         ::testing::Combine(enabled_test_solvers, ::testing::ValuesIn(get_files("test/solver/smt2")),
                                            ::testing::Values(Config::PreprocessingRunningFrequency::NEVER,
                                                              Config::PreprocessingRunningFrequency::ON_FIXED,
                                                              Config::PreprocessingRunningFrequency::ALWAYS)));

TEST_P(TestCompleteSmt2, Smt2InputAgainstExpectedOutput) {
  SmtSolver s{config_};
  const SmtResult result = s.Parse().result;
  EXPECT_EQ(s.GetExpected(), result);
}
