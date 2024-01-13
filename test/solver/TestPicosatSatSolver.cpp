/**
 * @file TestSolver.cpp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 */

#include <gtest/gtest.h>

#include <memory>

#include "dlinear/solver/PicosatSatSolver.h"

using dlinear::Config;
using dlinear::PicosatSatSolver;
using dlinear::SatSolver;
using std::unique_ptr;

class TestSolver : public ::testing::Test {
 protected:
  Config config_;
  explicit TestSolver(Config::LPSolver lp_solver = dlinear::Config::QSOPTEX) : config_{} {
    DLINEAR_LOG_INIT_VERBOSITY(2);
    config_.mutable_lp_solver() = lp_solver;
    config_.mutable_filename() = "test.smt2";
    config_.mutable_format() = Config::Format::AUTO;
  }
};

TEST_F(TestSolver, ConstructorDefault) { PicosatSatSolver s{}; }

TEST_F(TestSolver, ConstructorConfig) { PicosatSatSolver s{config_}; }

TEST_F(TestSolver, AddLiteral) {
  PicosatSatSolver s{config_};
  s.AddLiteral(1);
  EXPECT_TRUE(Infinity::IsInitialized());
}
