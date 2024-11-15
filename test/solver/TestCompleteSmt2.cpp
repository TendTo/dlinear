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

class TestCompleteSmt2 : public ::testing::TestWithParam<std::tuple<Config::LPSolver, std::string>> {
 protected:
  Config config_;

  TestCompleteSmt2() {
    const auto& [lp_solver, filename] = GetParam();
    config_.m_precision() = 0.0;
    config_.m_complete() = true;
    config_.m_timeout() = 30000;
    config_.m_format() = Config::Format::SMT2;
    config_.m_filename() = filename;
    config_.m_lp_solver() = lp_solver;
    config_.m_verify() = true;
    config_.m_bound_checking_frequency() = Config::RunningFrequency::NEVER;
    config_.m_simple_bound_propagation_frequency() = Config::RunningFrequency::NEVER;
    std::cout << "Testing " << filename << std::endl;
  }
};

INSTANTIATE_TEST_SUITE_P(TestCompleteSmt2, TestCompleteSmt2,
                         ::testing::Combine(enabled_test_solvers, ::testing::ValuesIn(GetFiles("test/solver/smt2"))));

TEST_P(TestCompleteSmt2, Smt2InputAgainstExpectedOutput) {
  if (config_.lp_solver() == Config::LPSolver::QSOPTEX) GTEST_SKIP();
  SmtSolver s{config_};
  const SmtSolverOutput result = s.Parse();

  // Ignore the test if the solver is not supported or if it's too slow
  if (result.result == SmtResult::ERROR || result.result == SmtResult::TIMEOUT) GTEST_SKIP();

  ASSERT_EQ(s.GetExpected(), result.result);
  if (result.is_sat()) {
    ASSERT_TRUE(s.Verify(result.complete_model));
  }
}
