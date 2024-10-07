/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gtest/gtest.h>

#include <memory>

#include "dlinear/solver/Context.h"
#include "test/solver/TestSolverUtils.h"

using dlinear::Config;
using dlinear::Context;
using dlinear::Variable;
using std::unique_ptr;

class TestContext : public ::testing::TestWithParam<Config::LPSolver> {
 protected:
  const Variable x_{"x"};
  const Variable y_{"Y"};
  Config config_;
  Context context_;
  explicit TestContext() : context_{config_} {
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
