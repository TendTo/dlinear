/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gtest/gtest.h>

#include <memory>

#include "dlinear/solver/SmtSolver.h"
#include "test/solver/TestSolverUtils.h"

using dlinear::Config;
using dlinear::Expression;
using dlinear::Formula;
using dlinear::SmtResult;
using dlinear::SmtSolver;
using dlinear::Variable;
using std::unique_ptr;

class TestSmtSolver : public ::testing::TestWithParam<Config::LPSolver> {
 protected:
  Config config_;
  const Variable x_{"x"}, y_{"y"}, z_{"z"};
  const Variable a_{"a", Variable::Type::BOOLEAN}, b_{"b", Variable::Type::BOOLEAN}, c_{"c", Variable::Type::BOOLEAN};
  explicit TestSmtSolver() : config_{} {
    config_.m_filename() = "test.smt2";
    config_.m_format() = Config::Format::AUTO;
  }
  void SetUp() override { config_.m_lp_solver() = GetParam(); }
};

INSTANTIATE_TEST_SUITE_P(TestSmtSolver, TestSmtSolver, enabled_test_solvers);

TEST_P(TestSmtSolver, CheckSatWrongFilename) {
  SmtSolver s{"test.err"};
  EXPECT_THROW(s.Parse(), std::runtime_error);
}

TEST_P(TestSmtSolver, CheckSatEmpty) {
  SmtSolver s{config_};
  EXPECT_EQ(s.CheckSat().result, SmtResult::SAT);
}

TEST_P(TestSmtSolver, CheckSatTrue) {
  SmtSolver s{config_};
  s.Assert(Expression{1} + 1 == 2);
  EXPECT_EQ(s.CheckSat().result, SmtResult::SAT);
}

TEST_P(TestSmtSolver, CheckUnsatFalse) {
  SmtSolver s{config_};
  s.Assert(Expression{1} + 1 == 3);
  EXPECT_EQ(s.CheckSat().result, SmtResult::UNSAT);
}

TEST_P(TestSmtSolver, CheckSatSimpleBound) {
  SmtSolver s{config_};
  s.Assert(x_ > 0);
  EXPECT_EQ(s.CheckSat().result, SmtResult::SAT);
}

TEST_P(TestSmtSolver, CheckSatSimpleBounds) {
  SmtSolver s{config_};
  s.Assert(x_ > 1);
  s.Assert(x_ < 11);
  s.Assert(y_ >= 0);
  s.Assert(y_ <= 10);
  s.Assert(z_ == -10);
  EXPECT_EQ(s.CheckSat().result, SmtResult::SAT);
}

TEST_P(TestSmtSolver, CheckUnsatConflictingAssertions) {
  SmtSolver s{config_};
  s.Assert(x_ > 0);
  s.Assert(x_ < 0);
  EXPECT_EQ(s.CheckSat().result, SmtResult::UNSAT);
}

TEST_P(TestSmtSolver, CheckSatBoolean) {
  SmtSolver s{config_};
  s.Assert(a_ && b_);
  s.Assert(a_ || b_);
  EXPECT_EQ(s.CheckSat().result, SmtResult::SAT);
}

TEST_P(TestSmtSolver, CheckSatTautology) {
  SmtSolver s{config_};
  s.Assert(a_ || !b_);
  s.Assert(!a_ || b_);
  EXPECT_EQ(s.CheckSat().result, SmtResult::SAT);
}

TEST_P(TestSmtSolver, CheckUnsatContradiction) {
  SmtSolver s{config_};
  s.Assert(a_ && !a_);
  EXPECT_EQ(s.CheckSat().result, SmtResult::UNSAT);
}

TEST_P(TestSmtSolver, CheckUnsatConflict) {
  SmtSolver s{config_};
  s.Assert(Formula{a_});
  s.Assert(!a_ && b_);
  EXPECT_EQ(s.CheckSat().result, SmtResult::UNSAT);
}