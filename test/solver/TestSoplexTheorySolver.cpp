/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <filesystem>
#include <memory>
#include <string_view>

#include "dlinear/solver/SoplexTheorySolver.h"

using dlinear::BoundPreprocessor;
using dlinear::BoundVectorMap;
using dlinear::Box;
using dlinear::Config;
using dlinear::Literal;
using dlinear::LiteralSet;
using dlinear::PredicateAbstractor;
using dlinear::SatResult;
using dlinear::SoplexTheorySolver;
using dlinear::Variable;
using std::unique_ptr;

class MockSoplexTheorySolver : public SoplexTheorySolver {
 public:
  explicit MockSoplexTheorySolver(PredicateAbstractor &predicate_abstractor)
      : SoplexTheorySolver{predicate_abstractor} {}
  MOCK_METHOD(void, AddLiteral, (const dlinear::Variable &formula_var, const dlinear::Formula &formula), (override));
  MOCK_METHOD(SoplexTheorySolver::Explanations, EnableLiteral, (const dlinear::Literal &lit), (override));
  MOCK_METHOD(SatResult, CheckSatCore, (mpq_class * actual_precision, SoplexTheorySolver::Explanations &explanation),
              (override));
  MOCK_METHOD(void, EnableSpxRow, (int, bool), (override));
};

class TestSoplexTheorySolver : public ::testing::TestWithParam<double> {
 protected:
  const Variable var_{"x"};
  Config config_;
  PredicateAbstractor abstractor_;
  MockSoplexTheorySolver s_;
  explicit TestSoplexTheorySolver() : config_{GetConfig()}, abstractor_{config_}, s_{abstractor_} {}
  static Config GetConfig() {
    Config config;
    config.m_precision() = 0;
    config.m_lp_solver() = Config::LPSolver::SOPLEX;
    return config;
  }
};

INSTANTIATE_TEST_SUITE_P(TestSoplexTheorySolver, TestSoplexTheorySolver, ::testing::Values(0.0, 0.1));

TEST_P(TestSoplexTheorySolver, AddVariable) {
  const int theory_col = 0;
  config_.m_precision() = GetParam();
  EXPECT_EQ(s_.theory_col_to_var().size(), 0u);

  s_.AddVariable(var_);
  EXPECT_EQ(s_.theory_col_to_var().size(), 1u);
  EXPECT_EQ(s_.theory_col_to_var().at(theory_col), var_);
  EXPECT_EQ(s_.var_to_theory_col().size(), 1u);
  EXPECT_EQ(s_.var_to_theory_col().at(var_.get_id()), theory_col);
  EXPECT_EQ(s_.fixed_theory_bounds().at(var_).active_lower_bound(), -soplex::infinity);
  EXPECT_EQ(s_.fixed_theory_bounds().at(var_).active_upper_bound(), soplex::infinity);
}

TEST_P(TestSoplexTheorySolver, EnableLiterals) {
  config_.m_precision() = GetParam();
  EXPECT_EQ(s_.theory_col_to_var().size(), 0u);

  std::vector<Literal> literals{{var_, true}, {var_, false}, {var_, false}};
  EXPECT_CALL(s_, EnableLiteral(testing::_)).Times(static_cast<int>(literals.size()));

  s_.EnableLiterals(literals);
}

TEST_P(TestSoplexTheorySolver, ResetBoxEmpty) {
  config_.m_precision() = GetParam();
  s_.AddVariable(var_);

  EXPECT_EQ(s_.fixed_theory_bounds().at(var_).active_lower_bound(), -soplex::infinity);
  EXPECT_EQ(s_.fixed_theory_bounds().at(var_).active_upper_bound(), soplex::infinity);
  s_.Consolidate(Box{Config::LPSolver::SOPLEX});

  EXPECT_EQ(s_.fixed_theory_bounds().at(var_).active_lower_bound(), -soplex::infinity);
  EXPECT_EQ(s_.fixed_theory_bounds().at(var_).active_upper_bound(), soplex::infinity);
}

TEST_P(TestSoplexTheorySolver, ResetBoxBounds) {
  mpq_class lb = 5, ub = 10;
  Box box{Config::LPSolver::SOPLEX};
  box.Add(var_, lb, ub);
  config_.m_precision() = GetParam();
  s_.AddVariable(var_);

  EXPECT_EQ(s_.fixed_theory_bounds().at(var_).active_lower_bound(), -soplex::infinity);
  EXPECT_EQ(s_.fixed_theory_bounds().at(var_).active_upper_bound(), soplex::infinity);
  s_.Consolidate(box);

  EXPECT_EQ(s_.fixed_theory_bounds().at(var_).active_lower_bound(), lb);
  EXPECT_EQ(s_.fixed_theory_bounds().at(var_).active_upper_bound(), ub);
}
