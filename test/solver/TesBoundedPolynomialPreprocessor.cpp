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
            .AddBound(dlinear::Bound::Parse(lit, pa_formula));
        std::cout << "Simple bound: " << lit << " " << pa_formula << std::endl;
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

TEST_F(TestEqBinomialPreprocessor, ProcessPropagateIncompatibleDifferentEqBounds) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x1_ == 10 * x2_, x2_ == x3_, x3_ == val});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.cbegin(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2]));
}

TEST_F(TestEqBinomialPreprocessor, ProcessPropagateIncompatibleDifferentEqBoundsDifferentEnds) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x1_ == 10 * x2_, x2_ == x3_, x3_ == mpq_class{val + 1}});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  ASSERT_EQ(explanations_.size(), 2u);

  for (const auto &explanation : explanations_) {
    switch (explanation.size()) {
      case 3:
        EXPECT_THAT(explanation, ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                 active_constraints_[2]));
        break;
      case 4:
        EXPECT_THAT(explanation, ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                 active_constraints_[3], active_constraints_[4]));
        break;
      default:
        FAIL();
    }
  }
}

TEST_F(TestEqBinomialPreprocessor, ProcessPropagateIncompatibleDifferentEqBoundsDifferentEndsAdvanced) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x1_ == 10 * x2_, x2_ == x3_, x2_ == 4 * x4_, x3_ == 13 * x4_,
                  x4_ == mpq_class{val + 1}});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 4u);
  ASSERT_EQ(explanations_.size(), 3u);

  for (const auto &explanation : explanations_) {
    switch (explanation.size()) {
      case 3:
        EXPECT_THAT(explanation, ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                 active_constraints_[2]));
        break;
      case 4:
        EXPECT_THAT(explanation, ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                 active_constraints_[4], active_constraints_[6]));
        break;
      case 5:
        EXPECT_THAT(explanation, ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                 active_constraints_[3], active_constraints_[5],
                                                                 active_constraints_[6]));
        break;
      default:
        FAIL();
    }
  }
}

TEST_F(TestEqBinomialPreprocessor, ProcessPropagateMultipleOrigins) {
  const mpq_class val = 7;
  const mpq_class val2 = val + 1;
  /**
   *  x1 - x2 - x3 - V
   *   |
   *  x4 - x6 - V2
   *   |
   *  x5 - x7 - V2
   *   |
   *  x8 - V2
   */
  AddConstraints({x1_ == x2_, x2_ == x3_, x3_ == val, x1_ == x4_, x4_ + x5_ + x6_ == mpq_class(2 * val2),
                  x5_ + x7_ + x8_ == mpq_class(3 * val2), x6_ == val2, x7_ == val2, x8_ == val2});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  EXPECT_EQ(preprocessor_.env().size(), 8u);
  ASSERT_EQ(preprocessor_.var_bounds().size(), 8u);
  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.cbegin(), ::testing::UnorderedElementsAreArray(active_constraints_));
}

TEST_F(TestEqBinomialPreprocessor, ProcessPropagateMultipleOriginsCommonOrigin) {
  const mpq_class val = 7;
  const mpq_class val2 = val + 1;
  /**
   *  x1 - x2 - x3 - V
   *   |
   *  x4 - x6 - V2
   *   |
   *  x5 - x7
   *   |    |
   *  x8 - x9 - V2
   */
  AddConstraints({x1_ == x2_, x2_ == x3_, x3_ == val, x1_ == x4_, x4_ + x5_ + x6_ == mpq_class(2 * val2),
                  x5_ + x7_ + x8_ == mpq_class(3 * val2), x6_ == val2, x7_ == x9_, x8_ == x9_, x9_ == val2});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  EXPECT_EQ(preprocessor_.env().size(), 9u);
  ASSERT_EQ(preprocessor_.var_bounds().size(), 9u);
  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.cbegin(), ::testing::UnorderedElementsAreArray(active_constraints_));
}

TEST_F(TestEqBinomialPreprocessor, ProcessEvaluateViolation) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x2_ == x3_, x3_ == val, x4_ == (x1_ + x5_), x6_ == x2_, x5_ == x6_,
                  x7_ == mpq_class{val + 1}, x7_ == x4_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 7u);
  EXPECT_EQ(preprocessor_.env()[x1_], val);
  EXPECT_EQ(preprocessor_.env()[x2_], val);
  EXPECT_EQ(preprocessor_.env()[x3_], val);
  EXPECT_EQ(preprocessor_.env()[x4_], val + 1);
  EXPECT_EQ(preprocessor_.env()[x5_], val);
  EXPECT_EQ(preprocessor_.env()[x6_], val);
  EXPECT_EQ(preprocessor_.env()[x7_], val + 1);

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.cbegin(), ::testing::UnorderedElementsAreArray(active_constraints_));
}

TEST_F(TestEqBinomialPreprocessor, ProcessEvaluateViolationInInequalityBound) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x2_ == x3_, x3_ > val, x2_ == x4_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 4u);
  EXPECT_EQ(preprocessor_.env()[x1_], val);
  EXPECT_EQ(preprocessor_.env()[x2_], val);
  EXPECT_EQ(preprocessor_.env()[x4_], val);

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.cbegin(), ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                       active_constraints_[2], active_constraints_[3]));
}

TEST_F(TestEqBinomialPreprocessor, ProcessEvaluateViolationInComplexInequalityBound) {
  const mpq_class val = 7;
  AddConstraints({
      x1_ == val,                       // 0
      x1_ == x2_,                       // 1
      x2_ == x3_,                       // 2
      x3_ + x2_ != mpq_class(2 * val),  // 3
      x3_ + x2_<mpq_class(2 * val),     // 4
                x3_ + x2_>
                mpq_class(2 * val),     // 5
      x3_ + x2_ >= mpq_class(2 * val),  // 6
      x3_ + x2_ <= mpq_class(2 * val),  // 7
      x3_ + x2_ == mpq_class(2 * val),  // 8
      x2_ == x4_,
  });
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(preprocessor_.var_bounds().size(), 4u);
  EXPECT_EQ(preprocessor_.env()[x1_], val);
  EXPECT_EQ(preprocessor_.env()[x2_], val);
  EXPECT_EQ(preprocessor_.env()[x3_], val);
  EXPECT_EQ(preprocessor_.env()[x4_], val);

  ASSERT_THAT(explanations_.size(), 3u);
  EXPECT_THAT(*explanations_.cbegin(), ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                       active_constraints_[2], active_constraints_[3]));
  EXPECT_THAT(*std::next(explanations_.begin()),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[4]));
  EXPECT_THAT(*std::next(std::next(explanations_.begin())),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[5]));
}

TEST_F(TestEqBinomialPreprocessor, ProcessBoundSimpleEqBinomial) {
  const mpq_class val = 7;
  const mpq_class lb = (3 * val - 11) / 5;
  const mpq_class ub = (3 * val + 3 - 11) / 5;
  AddConstraints({
      x1_ > val,
      x1_ < mpq_class(val + 1),
      3 * x1_ == 5 * x2_ + 11,
  });
  ASSERT_TRUE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));
  ASSERT_TRUE(explanations_.empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 2u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x1_).active_lower_bound(), val);
  EXPECT_EQ(preprocessor_.var_bounds().at(x1_).active_upper_bound(), val + 1);
  EXPECT_EQ(preprocessor_.var_bounds().at(x2_).active_lower_bound(), lb);
  EXPECT_EQ(preprocessor_.var_bounds().at(x2_).active_upper_bound(), ub);
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundSimpleGeBinomial) {
  const mpq_class val = 7;
  const mpq_class lb = (3 * val - 11) / 5;
  const mpq_class ub = (3 * val + 3 - 11) / 5;
  AddConstraints({
      x1_ > val,
      x1_ < mpq_class(val + 1),
      3 * x1_ >= 5 * x2_ + 11,
  });
  ASSERT_TRUE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));
  ASSERT_TRUE(explanations_.empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 2u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x1_).active_lower_bound(), val);
  EXPECT_EQ(preprocessor_.var_bounds().at(x1_).active_upper_bound(), val + 1);
  EXPECT_FALSE(preprocessor_.var_bounds().at(x2_).IsLowerBounded());
  EXPECT_EQ(preprocessor_.var_bounds().at(x2_).active_upper_bound(), ub);
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundSimpleGtBinomial) {
  const mpq_class val = 7;
  const mpq_class ub = (3 * val + 3 - 11) / 5;
  AddConstraints({
      x1_ > val,
      x1_ < mpq_class(val + 1),
      3 * x1_ > 5 * x2_ + 11,
  });
  ASSERT_TRUE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));
  ASSERT_TRUE(explanations_.empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 2u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x1_).active_lower_bound(), val);
  EXPECT_EQ(preprocessor_.var_bounds().at(x1_).active_upper_bound(), val + 1);
  EXPECT_FALSE(preprocessor_.var_bounds().at(x2_).IsLowerBounded());
  EXPECT_EQ(preprocessor_.var_bounds().at(x2_).active_upper_bound(), ub);
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundSimpleLeBinomial) {
  const mpq_class val = 7;
  const mpq_class lb = (3 * val - 11) / 5;
  AddConstraints({
      x1_ > val,
      x1_ < mpq_class(val + 1),
      3 * x1_ <= 5 * x2_ + 11,
  });
  ASSERT_TRUE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));
  ASSERT_TRUE(explanations_.empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 2u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x1_).active_lower_bound(), val);
  EXPECT_EQ(preprocessor_.var_bounds().at(x1_).active_upper_bound(), val + 1);
  EXPECT_EQ(preprocessor_.var_bounds().at(x2_).active_lower_bound(), lb);
  EXPECT_FALSE(preprocessor_.var_bounds().at(x2_).IsUpperBounded());
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundNegativeLeBinomial) {
  const mpq_class val = 7;
  const mpq_class lb = (3 * val - 11) / 5;
  AddConstraints({
      x1_ > val,
      x1_ < mpq_class(val + 1),
      3 * x1_ <= 5 * x2_ + 11,
  });
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));
  ASSERT_TRUE(explanations_.empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 2u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x1_).active_lower_bound(), val);
  EXPECT_EQ(preprocessor_.var_bounds().at(x1_).active_upper_bound(), val + 1);
  EXPECT_EQ(preprocessor_.var_bounds().at(x2_).active_lower_bound(), lb);
  EXPECT_FALSE(preprocessor_.var_bounds().at(x2_).IsUpperBounded());
}

TEST_F(TestEqBinomialPreprocessor, ProcessBoundInferEq) {
  const mpq_class val = 7;
  const mpq_class lb = (3 * val - 11) / 5;
  const Variable x11_{"x11"}, x13_{"x13"}, x16_{"x16"}, x87{"x87"}, L52{"L52"}, v_86{"v_86"}, ITE3{"ITE3"},
      ITE2{"ITE2"}, ITE10{"ITE10"}, L46{"L46"}, ITE11{"ITE11"};
  AddConstraints({
      6 * x13_ - 5 * x16_ <= 40,  // 0
      x16_ != 40,                 // 1
      x3_ == x13_,                // 2
      x7_ == 2,                   // 3
      x3_ == 20,                  // 4
      x2_ - L46 == -2,            // 5
      6 * x2_ - L52 == -10,       // 6
      x6_ == ITE3,                // 7
      ITE2 == ITE3,               // 8
      x16_ == ITE2,               // 9
      x6_ != 10,                  // 10
      x11_ == ITE10,              // 11
      L46 == ITE11,               // 12
      x6_ == ITE10,               // 13
      x7_ == ITE11,               // 14
      x2_ + 2 * x11_ >= 20,       // 15
      x11_ <= L52,                // 16
  });
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.cbegin(),
              ::testing::UnorderedElementsAre(active_constraints_[3], active_constraints_[5], active_constraints_[6],
                                              active_constraints_[10], active_constraints_[11], active_constraints_[12],
                                              active_constraints_[13], active_constraints_[14], active_constraints_[15],
                                              active_constraints_[16]));
}

TEST_F(TestEqBinomialPreprocessor, ProcessBoundLowerBoundMinimalExplanation) {
  AddConstraints({x1_ == x2_, x3_ == x2_, x3_ <= -100, x1_ > -1, x1_ <= 1});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.cbegin(), ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                       active_constraints_[2], active_constraints_[3]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundUpperBoundMinimalExplanation) {
  AddConstraints({x1_ == x2_, x3_ == x2_, x3_ >= 100, x1_ > -1, x1_ <= 1});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.cbegin(), ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                       active_constraints_[2], active_constraints_[4]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundEqBoundMinimalExplanation) {
  AddConstraints({x1_ == x2_, x3_ == x2_, x3_ >= 100, x1_ == 1});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.cbegin(), ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                       active_constraints_[2], active_constraints_[3]));
}

// TODO(tend): support single bounded variables propagation
// TEST_F(TestBoundPreprocessor, ProcessBoundBoundedPropagation) {
//   AddConstraints({x1_ >= 1, x2_ <= 1, x3_ == x1_, x3_ == x2_});
//   ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));
//
//   ASSERT_TRUE(explanations_.empty());
//   ASSERT_EQ(preprocessor_.env().size(), 1u);
//   EXPECT_EQ(preprocessor_.env()[x3_], 1);
//
//   ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
//   EXPECT_EQ(preprocessor_.var_bounds().at(x1_).active_lower_bound(), 1);
//   EXPECT_EQ(preprocessor_.var_bounds().at(x2_).active_upper_bound(), 1);
//   EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_lower_bound(), 1);
//   EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_upper_bound(), 1);
// }
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedEqPropagationSum) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ == x1_ + x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_TRUE(preprocessor_.env().empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_lower_bound(), -1);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_upper_bound(), 3);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedEqPropagationDifference) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ == x1_ - x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_TRUE(preprocessor_.env().empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_lower_bound(), -3);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_upper_bound(), 1);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedEqPropagationEqualBounds) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, x3_ == x1_ - x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_EQ(preprocessor_.env().size(), 3u);
  EXPECT_EQ(preprocessor_.env()[x1_], 1);
  EXPECT_EQ(preprocessor_.env()[x2_], 2);
  EXPECT_EQ(preprocessor_.env()[x3_], -1);

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_lower_bound(), -1);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_upper_bound(), -1);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}

TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedLePropagationSum) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ <= x1_ + x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_TRUE(preprocessor_.env().empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_upper_bound(), 3);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedLePropagationDifference) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ <= x1_ - x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_TRUE(preprocessor_.env().empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_upper_bound(), 1);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[2], active_constraints_[4]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedLePropagationEqualBounds) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, x3_ <= x1_ - x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_EQ(preprocessor_.env().size(), 2u);
  EXPECT_EQ(preprocessor_.env()[x1_], 1);
  EXPECT_EQ(preprocessor_.env()[x2_], 2);

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_upper_bound(), -1);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}

TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedGePropagationSum) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ >= x1_ + x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_TRUE(preprocessor_.env().empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_lower_bound(), -1);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[2], active_constraints_[4]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedGePropagationDifference) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ >= x1_ - x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_TRUE(preprocessor_.env().empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_lower_bound(), -3);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedGePropagationEqualBounds) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, x3_ >= x1_ - x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_EQ(preprocessor_.env().size(), 2u);
  EXPECT_EQ(preprocessor_.env()[x1_], 1);
  EXPECT_EQ(preprocessor_.env()[x2_], 2);

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_lower_bound(), -1);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}

TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedEqPropagationSumNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ == x1_ + x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_TRUE(preprocessor_.env().empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_lower_bound(), -3);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_upper_bound(), 1);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedEqPropagationDifferenceNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ == x1_ - x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_TRUE(preprocessor_.env().empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_lower_bound(), -1);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_upper_bound(), 3);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedEqPropagationEqualBoundsNegative) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, -x3_ == x1_ - x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_EQ(preprocessor_.env().size(), 3u);
  EXPECT_EQ(preprocessor_.env()[x1_], 1);
  EXPECT_EQ(preprocessor_.env()[x2_], 2);
  EXPECT_EQ(preprocessor_.env()[x3_], 1);

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_lower_bound(), 1);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_upper_bound(), 1);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}

TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedLePropagationSumNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ <= x1_ + x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_TRUE(preprocessor_.env().empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_lower_bound(), -3);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedLePropagationDifferenceNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ <= x1_ - x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_TRUE(preprocessor_.env().empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_lower_bound(), -1);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[2], active_constraints_[4]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedLePropagationEqualBoundsNegative) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, -x3_ <= x1_ - x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_EQ(preprocessor_.env().size(), 2u);
  EXPECT_EQ(preprocessor_.env()[x1_], 1);
  EXPECT_EQ(preprocessor_.env()[x2_], 2);

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_lower_bound(), 1);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}

TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedGePropagationSumNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ >= x1_ + x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_TRUE(preprocessor_.env().empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_upper_bound(), 1);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[2], active_constraints_[4]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedGePropagationDifferenceNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ >= x1_ - x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_TRUE(preprocessor_.env().empty());

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_upper_bound(), 3);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedGePropagationEqualBoundsNegative) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, -x3_ >= x1_ - x2_});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_TRUE(explanations_.empty());
  ASSERT_EQ(preprocessor_.env().size(), 2u);
  EXPECT_EQ(preprocessor_.env()[x1_], 1);
  EXPECT_EQ(preprocessor_.env()[x2_], 2);

  ASSERT_EQ(preprocessor_.var_bounds().size(), 3u);
  EXPECT_EQ(preprocessor_.var_bounds().at(x3_).active_upper_bound(), 1);

  ASSERT_EQ(preprocessor_.var_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(preprocessor_.var_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}

TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedEqViolationLowerBound) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ == x1_ + x2_, x3_ >= 4});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.begin(), ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[3],
                                                                      active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedEqViolationUpperBound) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ == x1_ + x2_, x3_ <= -2});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.begin(), ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[2],
                                                                      active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedEqViolationDifferenceUpperBound) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ == x1_ - x2_, x3_ <= -4});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.begin(), ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[3],
                                                                      active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedEqViolationDifferenceLowerBound) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ == x1_ - x2_, x3_ >= 2});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.begin(), ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[2],
                                                                      active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedEqViolationEqLowerBound) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, x3_ == x1_ - x2_, x3_ >= 2});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.begin(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedEqViolationEqUpperBound) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, x3_ == x1_ - x2_, x3_ <= -2});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.begin(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4], active_constraints_[5]));
}

TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedLeViolationLower) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ <= x1_ + x2_, x3_ >= 4});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.begin(), ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[3],
                                                                      active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedLeViolationDifference) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ <= x1_ - x2_, x3_ >= 2});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.begin(), ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[2],
                                                                      active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedLeViolationEqualBounds) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, x3_ <= x1_ - x2_, x3_ >= 0});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.begin(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4], active_constraints_[5]));
}

TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedLeViolationLowerNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ <= x1_ + x2_, x3_ <= -100});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.begin(), ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[3],
                                                                      active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedLeViolationDifferenceNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ <= x1_ - x2_, x3_ <= -100});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.begin(), ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[2],
                                                                      active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestEqBinomialPreprocessor, ProcessBoundBoundedLeViolationEqualBoundsNegative) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, -x3_ <= x1_ - x2_, x3_ <= -100});
  ASSERT_FALSE(preprocessor_.Process(Config::ExecutionStep::ALWAYS, conflict_cb_));

  ASSERT_EQ(explanations_.size(), 1u);
  EXPECT_THAT(*explanations_.begin(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4], active_constraints_[5]));
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