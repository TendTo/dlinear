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
using dlinear::get_files;
using dlinear::SmtSolver;
using dlinear::SmtSolverOutput;

class TestDeltaVnnlib : public ::testing::TestWithParam<std::tuple<Config::LPSolver, double, std::string>> {
 protected:
  Config config_;

  TestDeltaVnnlib() {
    const auto& [lp_solver, precision, filename] = GetParam();
    config_.m_precision() = precision;
    config_.m_complete() = false;
    config_.m_format() = Config::Format::VNNLIB;
    config_.m_filename() = filename;
    config_.m_onnx_file() = filename.substr(0, filename.find('.')) + ".onnx";
    config_.m_lp_solver() = lp_solver;
    config_.m_bound_propagation_type() = Config::BoundPropagationType::BOUND_POLYNOMIAL;
    config_.m_bound_propagation_frequency() = Config::PreprocessingRunningFrequency::ALWAYS;
    config_.m_bound_implication_frequency() = Config::PreprocessingRunningFrequency::ALWAYS;
    std::cout << "Testing " << filename << std::endl;
  }
};

INSTANTIATE_TEST_SUITE_P(TestDeltaVnnlib, TestDeltaVnnlib,
                         ::testing::Combine(enabled_test_solvers, ::testing::Values(0.0, 0.1),
                                            ::testing::ValuesIn(get_files("test/solver/vnnlib", ".vnnlib"))));

TEST_P(TestDeltaVnnlib, VnnlibInputAgainstExpectedOutput) {
  if (config_.lp_solver() == Config::LPSolver::QSOPTEX) GTEST_SKIP();
  SmtSolver s{config_};
  const SmtSolverOutput result = s.Parse();
  ASSERT_TRUE(delta_match_expected(result, s.GetExpected()));
}
