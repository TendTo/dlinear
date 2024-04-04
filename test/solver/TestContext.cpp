/**
 * @file TestContext.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include <memory>

#include "dlinear/solver/Context.h"
#include "test/solver/TestSolverUtils.h"
#include "test/symbolic/TestSymbolicUtils.h"

using dlinear::Config;
using dlinear::Context;
using std::unique_ptr;

class TestContext : public ::testing::TestWithParam<Config::LPSolver> {
  const DrakeSymbolicGuard guard_;

 protected:
  const Variable x_{"x"};
  const Variable y_{"Y"};
  Config config_;
  Context context_;
  explicit TestContext() : guard_{GetParam()}, context_{config_} {
    config_.m_lp_solver() = GetParam();
    context_.DeclareVariable(x_);
    context_.DeclareVariable(y_);
  }
};

INSTANTIATE_TEST_SUITE_P(TestContext, TestContext, enabled_test_solvers);

TEST_P(TestContext, Constructor) { EXPECT_NO_THROW(Context ctx{config_}); }

TEST_P(TestContext, DeclareVariable) {
  Context ctx{config_};
  ctx.DeclareVariable(x_);
  EXPECT_EQ(ctx.box().size(), 1);
  ctx.DeclareVariable(x_);  // Should not add another variable
  EXPECT_EQ(ctx.box().size(), 1);
}

TEST_P(TestContext, AddMultipleVariables) {
  Context ctx{config_};
  ctx.DeclareVariable(x_);
  EXPECT_EQ(ctx.box().size(), 1);
  ctx.DeclareVariable(y_);
  EXPECT_EQ(ctx.box().size(), 2);
}
