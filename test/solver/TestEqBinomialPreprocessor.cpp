/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "dlinear/solver/theory_solver/qf_lra/EqBinomialPreprocessor.h"
#include "dlinear/solver/theory_solver/qf_lra/QfLraTheorySolver.h"

using dlinear::BoundVectorMap;
using dlinear::Config;
using dlinear::Environment;
using dlinear::EqBinomialPreprocessor;
using dlinear::Explanation;
using dlinear::Formula;
using dlinear::IsSimpleBound;
using dlinear::Literal;
using dlinear::LiteralSet;
using dlinear::PredicateAbstractor;
using dlinear::QfLraTheorySolver;
using dlinear::Variable;
using Explanations = std::set<LiteralSet>;

class MockTheorySolver final : public QfLraTheorySolver {
 public:
  explicit MockTheorySolver(const PredicateAbstractor &pa) : QfLraTheorySolver{pa} {}
  MOCK_METHOD(void, AddLiteral, (const Variable &, const Formula &), (override));
  MOCK_METHOD(void, AddVariable, (const Variable &), (override));
  MOCK_METHOD(bool, EnableLiteral, (const Literal &, const dlinear::ConflictCallback &), (override));
  MOCK_METHOD(LiteralSet, enabled_literals, (), (const, override));
  MOCK_METHOD(dlinear::TheoryResult, CheckSatCore, (mpq_class *, const dlinear::ConflictCallback &), (override));
  MOCK_METHOD(void, CreateCheckpoint, (), (override));
  MOCK_METHOD(void, UpdateModelSolution, (), (override));
};

class TestEqBinomialPreprocessor : public ::testing::Test {
 protected:
  Config config_{std::string{"input.smt2"}};
  PredicateAbstractor pa_{config_};
  MockTheorySolver theory_solver_{pa_};
  EqBinomialPreprocessor preprocessor_{theory_solver_, std::make_shared<BoundVectorMap>(),
                                       std::make_shared<Environment>(), "TestBoundPreprocessor"};
  BoundVectorMap &theory_bounds_{const_cast<BoundVectorMap &>(preprocessor_.var_bounds())};
  const Variable x1_{"x1"}, x2_{"x2"}, x3_{"x3"}, x4_{"x4"}, x5_{"x5"}, x6_{"x6"}, x7_{"x7"}, x8_{"x8"}, x9_{"x9"},
      x10_{"x10"};
  const mpq_class inf_{100};
  const mpq_class ninf_{-100};
  std::vector<Literal> active_constraints_;
  Explanations explanations_;

  std::function<void(const Explanation &)> conflict_cb_ = [&](const Explanation &explanation) {
    explanations_.insert(explanation);
  };

  void AddConstraints(const std::initializer_list<Formula> formulas) {
    for (const auto &formula : formulas) {
      for (const Variable &var : formula.GetFreeVariables()) {
        preprocessor_.AddVariable(var);
        const_cast<BoundVectorMap &>(preprocessor_.var_bounds()).insert({var, {ninf_, inf_}});
      }
      const Formula flattened = pa_.Process(formula);
      const Variable &var = is_negation(flattened) ? get_variable(get_operand(flattened)) : get_variable(flattened);
      const Literal lit{var, !is_negation(flattened)};
      if (const Formula &pa_formula = pa_[lit.var]; IsSimpleBound(pa_formula)) {
        const Variable &real_var = *pa_formula.GetFreeVariables().cbegin();
        const_cast<BoundVectorMap &>(preprocessor_.var_bounds())
            .at(real_var)
            .AddBound(dlinear::Bound::Parse(lit, pa_formula), [](const Explanation &e) {
              fmt::println("Conflict: {}", e);
              std::cout << std::endl;
              FAIL();
            });
      }
      preprocessor_.EnableLiteral(lit, conflict_cb_);
      active_constraints_.push_back(lit);
    }
  }
};

TEST_F(TestEqBinomialPreprocessor, Constructor) {
  const auto var_bounds{std::make_shared<BoundVectorMap>()};
  const auto env{std::make_shared<Environment>()};
  const EqBinomialPreprocessor bound_preprocessor{theory_solver_, var_bounds, env, "MyBoundPreprocessor"};
  EXPECT_EQ(&bound_preprocessor.theory_solver().predicate_abstractor(), &pa_);
  EXPECT_NE(&bound_preprocessor.var_bounds(), &theory_solver_.vars_bounds());
  EXPECT_EQ(bound_preprocessor.stats().class_name(), "MyBoundPreprocessor");
}

TEST_F(TestEqBinomialPreprocessor, ProcessSetEnvironment) {
  AddConstraints({x1_ == 0, x4_ == 0});
  ASSERT_TRUE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 2u);
  EXPECT_EQ(preprocessor_.env().size(), 2u);
  EXPECT_EQ(preprocessor_.env()[x1_], 0);
  EXPECT_EQ(preprocessor_.env()[x4_], 0);
}

TEST_F(TestEqBinomialPreprocessor, ProcessPropagateLinearPath) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x2_ == x3_, x3_ == x4_});
  ASSERT_TRUE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 4u);
  EXPECT_EQ(preprocessor_.env().size(), 4u);
  EXPECT_EQ(preprocessor_.env()[x1_], val);
  EXPECT_EQ(preprocessor_.env()[x2_], val);
  EXPECT_EQ(preprocessor_.env()[x3_], val);
  EXPECT_EQ(preprocessor_.env()[x4_], val);
}
TEST_F(TestEqBinomialPreprocessor, ProcessPropagateLinearPathConstant) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ + 1 == x2_, x2_ + 2 == x3_, x3_ + 5 == x4_});
  ASSERT_TRUE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 4u);
  EXPECT_EQ(preprocessor_.env().size(), 4u);
  EXPECT_EQ(preprocessor_.env()[x1_], val);
  EXPECT_EQ(preprocessor_.env()[x2_], val + 1);
  EXPECT_EQ(preprocessor_.env()[x3_], val + 3);
  EXPECT_EQ(preprocessor_.env()[x4_], val + 8);
}
TEST_F(TestEqBinomialPreprocessor, ProcessPropagateLinearPathConstantFromRight) {
  const mpq_class val = 7;
  AddConstraints({x1_ == x2_ + 5, x2_ == x3_ + 2, x3_ == x4_ + 1, x4_ == val});
  ASSERT_TRUE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 4u);
  EXPECT_EQ(preprocessor_.env().size(), 4u);
  EXPECT_EQ(preprocessor_.env()[x1_], val + 8);
  EXPECT_EQ(preprocessor_.env()[x2_], val + 3);
  EXPECT_EQ(preprocessor_.env()[x3_], val + 1);
  EXPECT_EQ(preprocessor_.env()[x4_], val);
}
TEST_F(TestEqBinomialPreprocessor, ProcessPropagateLinearPathCoefficient) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, 2 * x1_ == 5 * x2_, 3 * x2_ == 4 * x3_, 5 * x3_ == 7 * x4_});
  ASSERT_TRUE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 4u);
  EXPECT_EQ(preprocessor_.env().size(), 4u);
  EXPECT_EQ(preprocessor_.env()[x1_], val);
  EXPECT_EQ(preprocessor_.env()[x2_], val * 2 / 5);
  EXPECT_EQ(preprocessor_.env()[x3_], val * 6 / 20);
  EXPECT_EQ(preprocessor_.env()[x4_], val * 30 / 140);
}
TEST_F(TestEqBinomialPreprocessor, ProcessPropagateLinearPathCoefficientConstant) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, 2 * x1_ + 1 == 5 * x2_, 3 * x2_ + 2 == 4 * x3_, 5 * x3_ + 3 == 7 * x4_});
  ASSERT_TRUE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 4u);
  EXPECT_EQ(preprocessor_.env().size(), 4u);
  EXPECT_EQ(preprocessor_.env()[x1_], val);
  EXPECT_EQ(preprocessor_.env()[x2_], (val * 2 + 1) / 5);
  EXPECT_EQ(preprocessor_.env()[x3_], (((val * 2 + 1) / 5 * 3) + 2) / 4);
  EXPECT_EQ(preprocessor_.env()[x4_], (((((val * 2 + 1) / 5 * 3) + 2) / 4) * 5 + 3) / 7);
}
TEST_F(TestEqBinomialPreprocessor, ProcessPropagateLinearPathCoefficientConstantFromRight) {
  const mpq_class val = 7;
  AddConstraints({x4_ == val, 2 * x4_ + 1 == 5 * x3_, 3 * x3_ + 2 == 4 * x2_, 5 * x2_ + 3 == 7 * x1_});
  ASSERT_TRUE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 4u);
  EXPECT_EQ(preprocessor_.env().size(), 4u);
  EXPECT_EQ(preprocessor_.env()[x1_], (((((val * 2 + 1) / 5 * 3) + 2) / 4) * 5 + 3) / 7);
  EXPECT_EQ(preprocessor_.env()[x2_], (((val * 2 + 1) / 5 * 3) + 2) / 4);
  EXPECT_EQ(preprocessor_.env()[x3_], (val * 2 + 1) / 5);
  EXPECT_EQ(preprocessor_.env()[x4_], val);
}

TEST_F(TestEqBinomialPreprocessor, ProcessPropagateLinearPathBothEnds) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x2_ == x3_, x3_ == x4_, x4_ == val});
  ASSERT_TRUE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 4u);
  EXPECT_EQ(preprocessor_.env().size(), 4u);
  EXPECT_EQ(preprocessor_.env()[x1_], val);
  EXPECT_EQ(preprocessor_.env()[x2_], val);
  EXPECT_EQ(preprocessor_.env()[x3_], val);
  EXPECT_EQ(preprocessor_.env()[x4_], val);
}

TEST_F(TestEqBinomialPreprocessor, ProcessPropagateSpread) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x2_ == x3_, x3_ == x4_, x2_ == x5_, x5_ == x6_, x3_ == x7_, x1_ == x8_,
                  x8_ == x9_, x9_ == x2_});
  ASSERT_TRUE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 9u);
  EXPECT_EQ(preprocessor_.env().size(), 9u);
  EXPECT_EQ(preprocessor_.env()[x1_], val);
  EXPECT_EQ(preprocessor_.env()[x2_], val);
  EXPECT_EQ(preprocessor_.env()[x3_], val);
  EXPECT_EQ(preprocessor_.env()[x4_], val);
  EXPECT_EQ(preprocessor_.env()[x5_], val);
  EXPECT_EQ(preprocessor_.env()[x6_], val);
  EXPECT_EQ(preprocessor_.env()[x7_], val);
  EXPECT_EQ(preprocessor_.env()[x8_], val);
  EXPECT_EQ(preprocessor_.env()[x9_], val);
}

TEST_F(TestEqBinomialPreprocessor, ProcessPropagateMultipleViolation) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x2_ == mpq_class{val + 1}, x2_ == x3_, x3_ == x4_, x4_ == x5_,
                  x5_ == mpq_class{val + 2}, x6_ == x7_, x7_ == mpq_class{val + 3}, x7_ == x8_, x8_ == x9_,
                  x9_ == mpq_class{val + 4}, x9_ == x10_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 10u);
  EXPECT_EQ(preprocessor_.env()[x1_], val);
  EXPECT_EQ(preprocessor_.env()[x2_], val + 1);
  EXPECT_EQ(preprocessor_.env()[x5_], val + 2);
  EXPECT_EQ(preprocessor_.env()[x7_], val + 3);
  EXPECT_EQ(preprocessor_.env()[x9_], val + 4);

  ASSERT_THAT(explanations_.size(), 3u);
  for (const auto &explanation : explanations_) {
    switch (explanation.size()) {
      case 3:
        EXPECT_THAT(explanation, ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                 active_constraints_[2]));
        break;
      case 4:
        EXPECT_THAT(explanation, ::testing::UnorderedElementsAre(active_constraints_[8], active_constraints_[9],
                                                                 active_constraints_[10], active_constraints_[11]));
        break;
      case 5:
        EXPECT_THAT(explanation, ::testing::UnorderedElementsAre(active_constraints_[2], active_constraints_[3],
                                                                 active_constraints_[4], active_constraints_[5],
                                                                 active_constraints_[6]));
        break;
      case 6:
        EXPECT_THAT(explanation, ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                 active_constraints_[3], active_constraints_[4],
                                                                 active_constraints_[5], active_constraints_[6]));
        break;
      default:
        FAIL();
    }
  }
}

TEST_F(TestEqBinomialPreprocessor, ProcessPropagateCompatibleDifferentEqBounds) {
  AddConstraints({x1_ == 0, x1_ == 2 * x2_, x1_ == 10 * x2_, x2_ == x3_, x2_ == 5 * x3_, x3_ == 0});
  ASSERT_TRUE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.env()[x1_], 0);
  EXPECT_EQ(preprocessor_.env()[x2_], 0);
  EXPECT_EQ(preprocessor_.env()[x2_], 0);
}

// TEST_F(TestBoundPreprocessor, ShouldPropagateTrue) {
//   AddConstraints({x1_ == 0});
//   preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_);
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(x1_ == x2_));
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(x1_ == x2_ + x2_));
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(x2_ + x1_ == x2_ + x2_));
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(x2_ + x1_ == x2_ + x2_ - x1_));
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(x1_ + x2_ == 0));
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(0 == x1_ + x2_));
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(2 * x1_ == 3 * x2_));
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(x1_ - x2_ == 0));
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(-x1_ == x2_));
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(2 * x1_ + 2 * x2_ == 3 * x2_));
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(x1_ + x2_ == 1));
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(x1_ == x2_ + 1));
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(1 == x1_ + x2_));
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(2 * x1_ + 1 == 3 * x2_));
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(x1_ - x2_ == 1));
//   EXPECT_TRUE(preprocessor_.ShouldPropagate(-x1_ == x2_ - 1));
// }
//
// TEST_F(TestBoundPreprocessor, ShouldPropagateFalse) {
//   AddConstraints({x1_ == 0});
//   preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_);
//   EXPECT_FALSE(preprocessor_.ShouldPropagate(x1_ == 0));
//   EXPECT_FALSE(preprocessor_.ShouldPropagate(0 == x2_));
//   EXPECT_FALSE(preprocessor_.ShouldPropagate(x1_ == x2_ + x3_));
//   EXPECT_FALSE(preprocessor_.ShouldPropagate(x1_ + x3_ == x2_));
//   EXPECT_FALSE(preprocessor_.ShouldPropagate(2 * x1_ + 3 * x2_ == 3 * x2_));
//   EXPECT_FALSE(preprocessor_.ShouldPropagate(x2_ + x1_ == x2_ + x2_ + x1_));
// }
//
// TEST_F(TestBoundPreprocessor, ExtractCoefficient) {
//   EXPECT_EQ(preprocessor_.ExtractCoefficient(x1_ == x2_), 1);
//   EXPECT_EQ(preprocessor_.ExtractCoefficient(x1_ + x2_ == 0), -1);
//   EXPECT_EQ(preprocessor_.ExtractCoefficient(2 * x1_ == 3 * x2_), mpq_class(3, 2));
//   EXPECT_EQ(preprocessor_.ExtractCoefficient(x1_ - x2_ == 0), 1);
//   EXPECT_EQ(preprocessor_.ExtractCoefficient(-x1_ == x2_), -1);
//   EXPECT_EQ(preprocessor_.ExtractCoefficient(x1_ + x2_ == 0), -1);
//   EXPECT_EQ(preprocessor_.ExtractCoefficient(0 == x1_ + x2_), -1);
//   EXPECT_EQ(preprocessor_.ExtractCoefficient(x2_ + x1_ == x2_ + x2_), 1);
//   EXPECT_EQ(preprocessor_.ExtractCoefficient(x2_ + x1_ == x2_ + x2_ - x1_), mpq_class(1, 2));
//   EXPECT_EQ(preprocessor_.ExtractCoefficient(2 * x1_ + 2 * x2_ == 3 * x2_), mpq_class(1, 2));
// }

TEST_F(TestEqBinomialPreprocessor, Stdcout) { EXPECT_NO_THROW(std::cout << preprocessor_ << std::endl); }
