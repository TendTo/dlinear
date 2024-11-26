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
using dlinear::SmtResult;
using dlinear::SmtSolver;
using dlinear::SmtSolverOutput;

class TestDeltaMps : public ::testing::TestWithParam<std::tuple<Config::LPSolver, std::string, double>> {
 protected:
  Config config_;

  TestDeltaMps() {
    const auto& [lp_solver, filename, precision] = GetParam();
    config_.m_precision() = precision;
    config_.m_complete() = false;
    config_.m_timeout() = 30000;
    config_.m_format() = Config::Format::MPS;
    config_.m_filename() = filename;
    config_.m_lp_solver() = lp_solver;
    config_.m_verify() = true;
    config_.m_bound_preprocess_step() = Config::ExecutionStep::NEVER;
    config_.m_simple_bound_propagation_step() = Config::ExecutionStep::NEVER;
    std::cout << "Testing " << filename << std::endl;
  }
};

INSTANTIATE_TEST_SUITE_P(TestDeltaMps, TestDeltaMps,
                         ::testing::Combine(enabled_test_solvers, ::testing::ValuesIn(GetFiles("test/solver/mps")),
                                            ::testing::Values(0.0, 0.1)));

TEST_P(TestDeltaMps, MpsInputAgainstExpectedOutput) {
  SmtSolver s{config_};
  s.Parse();
  const SmtSolverOutput result = s.CheckSat();

  // Ignore the test if the solver is not supported or if it's too slow
  if (result.result == SmtResult::ERROR || result.result == SmtResult::TIMEOUT) GTEST_SKIP();

  ASSERT_EQ(result.result, (result.result == SmtResult::DELTA_SAT ? SmtResult::DELTA_SAT : ~s.GetExpected()));
  if (result.is_sat() && config_.precision() == 0) {
    ASSERT_TRUE(s.Verify(result.complete_model));
  }
}
