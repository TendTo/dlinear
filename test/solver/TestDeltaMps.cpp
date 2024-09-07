/**
 * @file TestDeltaMps.cpp
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
using std::unique_ptr;

class TestMps : public ::testing::TestWithParam<
                    std::tuple<Config::LPSolver, std::string, double, Config::PreprocessingRunningFrequency>> {
 protected:
  Config config_;

  TestMps() {
    const auto& [lp_solver, filename, precision, frequency] = GetParam();
    config_.m_precision() = precision;
    config_.m_complete() = false;
    config_.m_format() = Config::Format::MPS;
    config_.m_filename() = filename;
    config_.m_lp_solver() = lp_solver;
    config_.m_bound_propagation_type() = Config::BoundPropagationType::AUTO;
    config_.m_bound_propagation_frequency() = frequency;
    config_.m_bound_implication_frequency() = frequency;
    std::cout << "Testing " << filename << std::endl;
  }
};

INSTANTIATE_TEST_SUITE_P(TestMps, TestMps,
                         ::testing::Combine(enabled_test_solvers, ::testing::ValuesIn(get_files("test/solver/mps")),
                                            ::testing::Values(0.0, 0.1),
                                            ::testing::Values(Config::PreprocessingRunningFrequency::NEVER,
                                                              Config::PreprocessingRunningFrequency::ALWAYS)));

TEST_P(TestMps, MpsInputAgainstExpectedOutput) {
  SmtSolver s{config_};
  s.Parse();
  const SmtResult result = s.CheckSat().result;
  EXPECT_THAT(delta_result(s.GetExpected()), ::testing::Contains(result));
}
