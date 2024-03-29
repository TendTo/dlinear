/**
 * @file TestSoplexTheorySolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <filesystem>
#include <memory>
#include <string_view>

#include "dlinear/solver/SoplexTheorySolver.h"
#include "test/solver/TestSolverUtils.h"
#include "test/symbolic/TestSymbolicUtils.h"

using dlinear::Box;
using dlinear::Config;
using dlinear::Literal;
using dlinear::LiteralSet;
using dlinear::PredicateAbstractor;
using dlinear::SatResult;
using dlinear::SoplexTheorySolver;
using dlinear::TheorySolverBoundVectorVector;
using dlinear::Variable;
using std::unique_ptr;

class MockSoplexTheorySolver : public SoplexTheorySolver {
 public:
  explicit MockSoplexTheorySolver(PredicateAbstractor &abstractor, const Config &config)
      : SoplexTheorySolver{abstractor, config} {}
  MOCK_METHOD(void, AddLiteral, (const dlinear::Literal &lit), (override));
  MOCK_METHOD(std::vector<LiteralSet>, EnableLiteral, (const dlinear::Literal &lit), (override));
  MOCK_METHOD(SatResult, CheckSat,
              (const dlinear::Box &box, mpq_class *actual_precision, dlinear::LiteralSet &explanation), (override));
  MOCK_METHOD(void, EnableSpxRow, (int, bool, const dlinear::Variables &), (override));
  const std::vector<Variable> &theory_col_to_var() const { return theory_col_to_var_; }
  const std::vector<Literal> &theory_row_to_lit() const { return theory_row_to_lit_; }
  const std::map<Variable::Id, int> &var_to_theory_col() const { return var_to_theory_col_; }
  const std::map<Variable::Id, int> &lit_to_theory_row() const { return lit_to_theory_row_; }
  const TheorySolverBoundVectorVector &theory_bounds() const { return theory_bounds_; }
};

class TestSoplexTheorySolver : public ::testing::TestWithParam<double> {
  const DrakeSymbolicGuard guard_;

 protected:
  Variable var_{"x"};
  Config config_;
  PredicateAbstractor abstractor_;
  explicit TestSoplexTheorySolver() : config_{} {
    config_.m_precision() = 0;
    config_.m_lp_solver() = Config::LPSolver::SOPLEX;
  }
};

INSTANTIATE_TEST_SUITE_P(TestSoplexTheorySolver, TestSoplexTheorySolver, ::testing::Values(0.0, 0.1));

TEST_P(TestSoplexTheorySolver, AddVariable) {
  const int theory_col = 0;
  config_.m_precision() = GetParam();
  MockSoplexTheorySolver s{abstractor_, config_};
  EXPECT_EQ(s.theory_col_to_var().size(), 0u);

  s.AddVariable(var_);
  EXPECT_EQ(s.theory_col_to_var().size(), 1u);
  EXPECT_EQ(s.theory_col_to_var().at(theory_col), var_);
  EXPECT_EQ(s.var_to_theory_col().size(), 1u);
  EXPECT_EQ(s.var_to_theory_col().at(var_.get_id()), theory_col);
  EXPECT_EQ(s.theory_bounds()[theory_col].active_lower_bound(), -soplex::infinity);
  EXPECT_EQ(s.theory_bounds()[theory_col].active_upper_bound(), soplex::infinity);
}

TEST_P(TestSoplexTheorySolver, EnableLiterals) {
  config_.m_precision() = GetParam();
  MockSoplexTheorySolver s{abstractor_, config_};
  EXPECT_EQ(s.theory_col_to_var().size(), 0u);

  std::vector<Literal> literals{{var_, true}, {var_, false}, {var_, false}};
  EXPECT_CALL(s, EnableLiteral(testing::_)).Times(static_cast<int>(literals.size()));

  s.EnableLiterals(literals);
}

TEST_P(TestSoplexTheorySolver, ResetBoxEmpty) {
  const int theory_col = 0;
  config_.m_precision() = GetParam();
  MockSoplexTheorySolver s{abstractor_, config_};
  s.AddVariable(var_);

  EXPECT_EQ(s.theory_bounds()[theory_col].active_lower_bound(), -soplex::infinity);
  EXPECT_EQ(s.theory_bounds()[theory_col].active_upper_bound(), soplex::infinity);
  s.Reset(Box{});

  EXPECT_EQ(s.theory_bounds()[theory_col].active_lower_bound(), -soplex::infinity);
  EXPECT_EQ(s.theory_bounds()[theory_col].active_upper_bound(), soplex::infinity);
}

TEST_P(TestSoplexTheorySolver, ResetBoxBounds) {
  const int theory_col = 0;
  mpq_class lb = 5, ub = 10;
  Box box{};
  box.Add(var_, lb, ub);
  config_.m_precision() = GetParam();
  MockSoplexTheorySolver s{abstractor_, config_};
  s.AddVariable(var_);

  EXPECT_EQ(s.theory_bounds()[theory_col].active_lower_bound(), -soplex::infinity);
  EXPECT_EQ(s.theory_bounds()[theory_col].active_upper_bound(), soplex::infinity);
  s.Reset(box);

  EXPECT_EQ(s.theory_bounds()[theory_col].active_lower_bound(), lb);
  EXPECT_EQ(s.theory_bounds()[theory_col].active_upper_bound(), ub);
}
