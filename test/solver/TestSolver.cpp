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

using dlinear::Config;
using dlinear::Infinity;
using dlinear::Solver;
using std::unique_ptr;

class TestSolver : public ::testing::Test {
 protected:
  Config config_;
  explicit TestSolver(Config::LPSolver lp_solver = dlinear::Config::LPSolver::QSOPTEX) : config_{} {
    DLINEAR_LOG_INIT_VERBOSITY(2);
    config_.m_lp_solver() = lp_solver;
    config_.m_filename() = "test.smt2";
    config_.m_format() = Config::Format::AUTO;
  }
};

TEST_F(TestSolver, ConstructorDefault) {
  {
    Solver s{};
    EXPECT_TRUE(Infinity::IsInitialized());
  }
  EXPECT_FALSE(Infinity::IsInitialized());
}

TEST_F(TestSolver, ConstructorFilename) {
  {
    Solver s{config_};
    EXPECT_TRUE(Infinity::IsInitialized());
  }
  EXPECT_FALSE(Infinity::IsInitialized());
}

TEST_F(TestSolver, ConstructorConfig) {
  {
    Solver s{config_};
    EXPECT_TRUE(Infinity::IsInitialized());
  }
  EXPECT_FALSE(Infinity::IsInitialized());
}

TEST_F(TestSolver, CheckSatWrongFilename) {
  Solver s{"test.err"};
  EXPECT_DEATH(s.CheckSat(), "Should not be reachable");
}
