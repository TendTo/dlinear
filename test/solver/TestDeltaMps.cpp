/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <filesystem>
#include <string_view>

#include "dlinear/solver/SmtSolver.h"
#include "test/solver/TestSolverUtils.h"

using dlinear::Config;
using dlinear::GetFiles;
using dlinear::SmtSolver;
using dlinear::SmtSolverOutput;

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
    config_.m_verify() = true;
    config_.m_bound_propagation_type() = Config::BoundPropagationType::AUTO;
    config_.m_bound_propagation_frequency() = frequency;
    config_.m_bound_implication_frequency() = frequency;
    std::cout << "Testing " << filename << std::endl;
  }
};

INSTANTIATE_TEST_SUITE_P(TestMps, TestMps,
                         ::testing::Combine(enabled_test_solvers, ::testing::ValuesIn(GetFiles("test/solver/mps")),
                                            ::testing::Values(0.0, 0.1),
                                            ::testing::Values(Config::PreprocessingRunningFrequency::NEVER,
                                                              Config::PreprocessingRunningFrequency::ALWAYS)));

TEST_P(TestMps, MpsInputAgainstExpectedOutput) {
  SmtSolver s{config_};
  s.Parse();
  const SmtSolverOutput result = s.CheckSat();
  ASSERT_TRUE(delta_match_expected(result, s.GetExpected()));
  if (result.is_sat() && config_.precision() == 0) {
    ASSERT_TRUE(s.Verify(result.complete_model));
  }
}
