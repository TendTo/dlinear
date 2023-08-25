/**
 * @file TestContext.cpp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 */

#include "dlinear/solver/Context.h"
#include "test/symbolic/TestSymbolicUtils.h"

#include <gtest/gtest.h>

#include <memory>

using std::unique_ptr;
using dlinear::Context;
using dlinear::Config;

class TestContext : public ::testing::Test {
  const DrakeSymbolicGuard guard_;
 protected:
  const Variable x_{"x"};
  const Variable y_{"Y"};
  Config config_;
  unique_ptr<Context> context_;
  explicit TestContext(Config::LPSolver lp_solver = dlinear::Config::QSOPTEX) : guard_{lp_solver},
                                                                                config_{},
                                                                                context_{
                                                                                    std::make_unique<Context>(config_)} {
    config_.mutable_lp_solver() = lp_solver;
  }
  void SetUp() override { context_->DeclareVariable(x_); }
};

TEST_F(TestContext, Constructor) {
  EXPECT_NO_THROW(Context ctx);
}

TEST_F(TestContext, DeclareVariable) {
  Context ctx;
  ctx.DeclareVariable(x_);
  EXPECT_EQ(ctx.box().size(), 1);
  ctx.DeclareVariable(x_); // Should not add another variable
  EXPECT_EQ(ctx.box().size(), 1);
}

TEST_F(TestContext, AddMultipleVariables) {
  Context ctx;
  ctx.DeclareVariable(x_);
  EXPECT_EQ(ctx.box().size(), 1);
  ctx.DeclareVariable(y_);
  EXPECT_EQ(ctx.box().size(), 2);
}
