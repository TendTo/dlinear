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

class TestDeltaVnnlib : public ::testing::TestWithParam<std::tuple<Config::LPSolver, std::string>> {
 protected:
  Config config_;

  TestDeltaVnnlib() {
    const auto& [lp_solver, filename] = GetParam();
    config_.m_precision() = 0.0;
    config_.m_complete() = true;
    config_.m_format() = Config::Format::VNNLIB;
    config_.m_filename() = filename;
    config_.m_onnx_file() = filename.substr(0, filename.find('.')) + ".onnx";
    config_.m_lp_solver() = lp_solver;
    config_.m_verify() = true;
    config_.m_bound_preprocess_step() = Config::ExecutionStep::ALWAYS;
    config_.m_simple_bound_propagation_step() = Config::ExecutionStep::ALWAYS;
    std::cout << "Testing " << filename << std::endl;
    DLINEAR_LOG_INIT_VERBOSITY(4);
  }
};

INSTANTIATE_TEST_SUITE_P(TestDeltaVnnlib, TestDeltaVnnlib,
                         ::testing::Combine(enabled_test_solvers,
                                            ::testing::ValuesIn(GetFiles("test/solver/vnnlib", ".vnnlib"))));

TEST_P(TestDeltaVnnlib, VnnlibInputAgainstExpectedOutput) {
  if (config_.lp_solver() == Config::LPSolver::QSOPTEX) GTEST_SKIP();
  SmtSolver s{config_};
  const SmtSolverOutput result = s.Parse();
  ASSERT_EQ(s.GetExpected(), result.result);
  if (result.is_sat()) {
    ASSERT_TRUE(s.Verify(result.complete_model));
  }
}
