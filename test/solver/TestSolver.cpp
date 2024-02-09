/**
 * @file TestSolver.cpp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 */
#include <gtest/gtest.h>

#include <memory>

#include "dlinear/solver/Solver.h"
#include "dlinear/util/Infinity.h"
#include "test/solver/TestSolverUtils.h"

using dlinear::Config;
using dlinear::Infinity;
using dlinear::Solver;
using std::unique_ptr;

class TestSolver : public ::testing::TestWithParam<Config::LPSolver> {
 protected:
  Config config_;
  explicit TestSolver() : config_{} {
    config_.m_filename() = "test.smt2";
    config_.m_format() = Config::Format::AUTO;
  }
  void SetUp() override { config_.m_lp_solver() = GetParam(); }
};

INSTANTIATE_TEST_SUITE_P(TestSolver, TestSolver, enabled_test_solvers);

TEST_P(TestSolver, ConstructorDefault) {
  {
    Solver s{};
    EXPECT_TRUE(Infinity::IsInitialized());
  }
  EXPECT_FALSE(Infinity::IsInitialized());
}

TEST_P(TestSolver, ConstructorFilename) {
  {
    Solver s{config_};
    EXPECT_TRUE(Infinity::IsInitialized());
  }
  EXPECT_FALSE(Infinity::IsInitialized());
}

TEST_P(TestSolver, ConstructorConfig) {
  {
    Solver s{config_};
    EXPECT_TRUE(Infinity::IsInitialized());
  }
  EXPECT_FALSE(Infinity::IsInitialized());
}

TEST_P(TestSolver, CheckSatWrongFilename) {
  Solver s{"test.err"};
  EXPECT_DEATH(s.CheckSat(), "");
}
