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

using dlinear::Config;
using dlinear::Solver;
using dlinear::SolverOutput;
using dlinear::SolverResult;
using std::unique_ptr;

std::vector<std::string> getFiles() {
  const std::string path = "test/solver/smt2";
  std::vector<std::string> files;
  for (const auto& entry : std::filesystem::directory_iterator(path)) {
    files.emplace_back(entry.path());
    std::cout << entry.path() << std::endl;
  }
  std::cout << "Found " << files.size() << " files in " << path << std::endl;
  return files;
}

class TestSmt2 : public ::testing::TestWithParam<std::tuple<Config::LPSolver, std::string, double>> {
 protected:
  Config config_;
  explicit TestSmt2() : config_{} {
    DLINEAR_LOG_INIT_VERBOSITY(2);
    config_.m_precision() = 0;
  }
};

INSTANTIATE_TEST_SUITE_P(TestSmt2, TestSmt2,
                         // TODO: add back QSOPTEX
                         ::testing::Combine(::testing::Values(Config::LPSolver::SOPLEX),
                                            ::testing::ValuesIn(getFiles()), ::testing::Values(0.0, 0.1)));

std::vector<SolverResult> expected_results(SolverResult res) {
  switch (res) {
    case SolverResult::SAT:
      return std::vector{SolverResult::SAT, SolverResult::DELTA_SAT};
    case SolverResult::DELTA_SAT:
      return std::vector{SolverResult::DELTA_SAT};
    case SolverResult::UNSAT:
      // return std::vector{SolverResult::UNSAT, SolverResult::DELTA_SAT};
      return std::vector{SolverResult::UNSAT, SolverResult::DELTA_SAT};
    case SolverResult::UNKNOWN:
      return std::vector{SolverResult::UNKNOWN};
    default:
      DLINEAR_UNREACHABLE();
  }
}

TEST_P(TestSmt2, TestSmt2InputAgainstExpectedOutputExhaustive) {
  const auto& [lp_solver, filename, precision] = GetParam();
  config_.m_filename() = filename;
  config_.m_lp_solver() = lp_solver;
  config_.m_precision() = precision;
  Solver s{config_};
  const SolverResult result = s.CheckSat().result();
  EXPECT_THAT(expected_results(s.GetExpected()), ::testing::Contains(result));
}

#if 0
TEST_P(TestSmt2, TestSmt2InputAgainstSolverOutput) {
  const auto& [_, filename] = GetParam();
  config_.mutable_filename() = filename;
  config_.mutable_lp_solver() = Config::LPSolver::QSOPTEX;
  Solver s_qsoptex{config_};
  config_.mutable_lp_solver() = Config::LPSolver::SOPLEX;
  Solver s_soplex{config_};
  EXPECT_EQ(s_qsoptex.CheckSat().result(), s_soplex.CheckSat().result());
}
#endif