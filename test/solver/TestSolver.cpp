/**
 * @file TestSolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include <memory>

#include "dlinear/solver/SmtSolver.h"
#include "dlinear/util/Infinity.h"
#include "test/solver/TestSolverUtils.h"

using dlinear::Config;
using dlinear::Infinity;
using dlinear::SmtSolver;
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
    SmtSolver s{};
    EXPECT_TRUE(Infinity::IsInitialized());
  }
  EXPECT_FALSE(Infinity::IsInitialized());
}

TEST_P(TestSolver, ConstructorFilename) {
  {
    SmtSolver s{config_};
    EXPECT_TRUE(Infinity::IsInitialized());
  }
  EXPECT_FALSE(Infinity::IsInitialized());
}

TEST_P(TestSolver, ConstructorConfig) {
  {
    SmtSolver s{config_};
    EXPECT_TRUE(Infinity::IsInitialized());
  }
  EXPECT_FALSE(Infinity::IsInitialized());
}

TEST_P(TestSolver, CheckSatWrongFilename) {
  SmtSolver s{"test.err"};
  EXPECT_DEATH(s.CheckSat(), "");
}
