/**
 * @file TestBoundPreprocessor.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "dlinear/solver/BoundPreprocessor.h"

using dlinear::BoundPreprocessor;
using dlinear::BoundVectorMap;
using dlinear::Config;
using dlinear::Formula;
using dlinear::Literal;
using dlinear::LiteralSet;
using dlinear::PredicateAbstractor;
using dlinear::Variable;
using Explanations = std::set<LiteralSet>;

class MockContextBoundPreprocessor : public BoundPreprocessor {
 public:
  explicit MockContextBoundPreprocessor(PredicateAbstractor &abstractor) : BoundPreprocessor{abstractor} {}
  auto ShouldEvaluate(const Formula &formula) { return BoundPreprocessor::ShouldEvaluate(Flatten(formula)); }
  auto ShouldPropagate(const Formula &formula) {
    return BoundPreprocessor::ShouldPropagateEqPolynomial(Flatten(formula));
  }
  auto ExtractEdge(const Formula &formula) {
    const auto [from, to] = BoundPreprocessor::ExtractBoundEdge(Flatten(formula));
    return std::make_pair(from, to);
  }
  auto ExtractCoefficient(const Formula &formula) {
    return BoundPreprocessor::ExtractEqBoundCoefficient(Flatten(formula));
  }

 private:
  Formula Flatten(const Formula &formula) {
    PredicateAbstractor pa{config()};
    const Variable var = get_variable(pa.Convert(formula));
    return pa.var_to_formula_map().at(var);
  }
};

class TestBoundPreprocessor : public ::testing::Test {
 protected:
  Config config_{std::string{"input.smt2"}};
  PredicateAbstractor pa_{config_};
  MockContextBoundPreprocessor bound_preprocessor_{pa_};
  BoundVectorMap &theory_bounds_{const_cast<BoundVectorMap &>(bound_preprocessor_.theory_bounds())};
  const Variable x1_{"x1"}, x2_{"x2"}, x3_{"x3"}, x4_{"x4"}, x5_{"x5"}, x6_{"x6"}, x7_{"x7"}, x8_{"x8"}, x9_{"x9"},
      x10_{"x10"};
  const mpq_class inf_{100};
  const mpq_class ninf_{-100};
  std::vector<Literal> active_constraints_;
  LiteralSet enabled_literals_;

  TestBoundPreprocessor() : bound_preprocessor_{pa_} {
    DLINEAR_LOG_INIT_VERBOSITY(0);
    config_.m_bound_propagation_type() = Config::BoundPropagationType::BOUND_POLYNOMIAL;
  }

  void AddConstraints(std::initializer_list<Formula> formulas) {
    for (const auto &formula : formulas) {
      for (const Variable &var : formula.GetFreeVariables()) bound_preprocessor_.AddVariable(var);
      const Formula flattened = pa_.Convert(formula);
      const Variable &var = is_negation(flattened) ? get_variable(get_operand(flattened)) : get_variable(flattened);
      const Literal lit{var, !is_negation(flattened)};
      bound_preprocessor_.EnableLiteral(lit);
      active_constraints_.push_back(lit);
      enabled_literals_.insert(lit);
    }
  }
};

TEST_F(TestBoundPreprocessor, Constructor) {
  BoundPreprocessor bound_preprocessor{pa_};
  EXPECT_EQ(&bound_preprocessor.predicate_abstractor(), &pa_);
}

TEST_F(TestBoundPreprocessor, AddConstraints) {
  AddConstraints({x1_ == 0, x2_ == 0, x3_ == x1_ + x2_ + x4_});
  EXPECT_EQ(&bound_preprocessor_.predicate_abstractor(), &pa_);

  EXPECT_EQ(bound_preprocessor_.predicate_abstractor().var_to_formula_map().size(), 3u);
  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 4u);
}

TEST_F(TestBoundPreprocessor, AddConstraintsPropagation) {
  AddConstraints({x1_ == 0, x1_ == x2_, x2_ == x3_, x3_ == 0});
  EXPECT_EQ(&bound_preprocessor_.predicate_abstractor(), &pa_);
  EXPECT_EQ(&bound_preprocessor_.theory_bounds(), &theory_bounds_);

  EXPECT_EQ(bound_preprocessor_.predicate_abstractor().var_to_formula_map().size(), 4u);
  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
}
TEST_F(TestBoundPreprocessor, AddConstraintsPropagationWithConstant) {
  AddConstraints({x1_ == 0, x1_ + 1 == x2_, x2_ + 3 == x3_, x3_ == 4});
  EXPECT_EQ(&bound_preprocessor_.predicate_abstractor(), &pa_);
  EXPECT_EQ(&bound_preprocessor_.theory_bounds(), &theory_bounds_);

  EXPECT_EQ(bound_preprocessor_.predicate_abstractor().var_to_formula_map().size(), 4u);
  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
}

TEST_F(TestBoundPreprocessor, EnableConstraintsPropagation) {
  AddConstraints({x1_ == 0, x1_ == x2_, x2_ == x3_, x3_ == 0});
  EXPECT_EQ(&bound_preprocessor_.predicate_abstractor(), &pa_);
  EXPECT_EQ(&bound_preprocessor_.theory_bounds(), &theory_bounds_);

  EXPECT_EQ(bound_preprocessor_.predicate_abstractor().var_to_formula_map().size(), 4u);
  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
}

TEST_F(TestBoundPreprocessor, ProcessSetEnvironment) {
  AddConstraints({x1_ == 0, x4_ == 0});
  bound_preprocessor_.Process(enabled_literals_);

  EXPECT_EQ(bound_preprocessor_.env().size(), 2u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], 0);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], 0);
}

TEST_F(TestBoundPreprocessor, ProcessPropagateLinearPath) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x2_ == x3_, x3_ == x4_});
  bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], val);
}
TEST_F(TestBoundPreprocessor, ProcessPropagateLinearPathConstant) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ + 1 == x2_, x2_ + 2 == x3_, x3_ + 5 == x4_});
  bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], val + 1);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], val + 3);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], val + 8);
}
TEST_F(TestBoundPreprocessor, ProcessPropagateLinearPathConstantFromRight) {
  const mpq_class val = 7;
  AddConstraints({x1_ == x2_ + 5, x2_ == x3_ + 2, x3_ == x4_ + 1, x4_ == val});
  bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val + 8);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], val + 3);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], val + 1);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], val);
}
TEST_F(TestBoundPreprocessor, ProcessPropagateLinearPathCoefficient) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, 2 * x1_ == 5 * x2_, 3 * x2_ == 4 * x3_, 5 * x3_ == 7 * x4_});
  bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], val * 2 / 5);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], val * 6 / 20);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], val * 30 / 140);
}
TEST_F(TestBoundPreprocessor, ProcessPropagateLinearPathCoefficientConstant) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, 2 * x1_ + 1 == 5 * x2_, 3 * x2_ + 2 == 4 * x3_, 5 * x3_ + 3 == 7 * x4_});
  bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], (val * 2 + 1) / 5);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], (((val * 2 + 1) / 5 * 3) + 2) / 4);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], (((((val * 2 + 1) / 5 * 3) + 2) / 4) * 5 + 3) / 7);
}
TEST_F(TestBoundPreprocessor, ProcessPropagateLinearPathCoefficientConstantFromRight) {
  const mpq_class val = 7;
  AddConstraints({x4_ == val, 2 * x4_ + 1 == 5 * x3_, 3 * x3_ + 2 == 4 * x2_, 5 * x2_ + 3 == 7 * x1_});
  bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], (((((val * 2 + 1) / 5 * 3) + 2) / 4) * 5 + 3) / 7);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], (((val * 2 + 1) / 5 * 3) + 2) / 4);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], (val * 2 + 1) / 5);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], val);
}

TEST_F(TestBoundPreprocessor, ProcessPropagateLinearPathBothEnds) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x2_ == x3_, x3_ == x4_, x4_ == val});
  bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], val);
}

TEST_F(TestBoundPreprocessor, ProcessPropagateSpread) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x2_ == x3_, x3_ == x4_, x2_ == x5_, x5_ == x6_, x3_ == x7_, x1_ == x8_,
                  x8_ == x9_, x9_ == x2_});
  bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 9u);
  EXPECT_EQ(bound_preprocessor_.env().size(), 9u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x5_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x6_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x7_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x8_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x9_], val);
}

TEST_F(TestBoundPreprocessor, ProcessPropagateMultipleViolation) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x2_ == mpq_class{val + 1}, x2_ == x3_, x3_ == x4_, x4_ == x5_,
                  x5_ == mpq_class{val + 2}, x6_ == x7_, x7_ == mpq_class{val + 3}, x7_ == x8_, x8_ == x9_,
                  x9_ == mpq_class{val + 4}, x9_ == x10_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 10u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], val + 1);
  EXPECT_EQ(bound_preprocessor_.env()[x5_], val + 2);
  EXPECT_EQ(bound_preprocessor_.env()[x7_], val + 3);
  EXPECT_EQ(bound_preprocessor_.env()[x9_], val + 4);

  ASSERT_THAT(explanations.size(), 3u);
  for (const auto &explanation : explanations) {
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

TEST_F(TestBoundPreprocessor, ProcessPropagateCompatibleDifferentEqBounds) {
  AddConstraints({x1_ == 0, x1_ == 2 * x2_, x1_ == 10 * x2_, x2_ == x3_, x2_ == 5 * x3_, x3_ == 0});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], 0);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], 0);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], 0);
  EXPECT_TRUE(explanations.empty());
}

TEST_F(TestBoundPreprocessor, ProcessPropagateIncompatibleDifferentEqBounds) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x1_ == 10 * x2_, x2_ == x3_, x3_ == val});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.cbegin(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2]));
}

TEST_F(TestBoundPreprocessor, ProcessPropagateIncompatibleDifferentEqBoundsDifferentEnds) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x1_ == 10 * x2_, x2_ == x3_, x3_ == mpq_class{val + 1}});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  ASSERT_EQ(explanations.size(), 2u);

  for (const auto &explanation : explanations) {
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

TEST_F(TestBoundPreprocessor, ProcessPropagateIncompatibleDifferentEqBoundsDifferentEndsAdvanced) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x1_ == 10 * x2_, x2_ == x3_, x2_ == 4 * x4_, x3_ == 13 * x4_,
                  x4_ == mpq_class{val + 1}});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 4u);
  ASSERT_EQ(explanations.size(), 3u);

  for (const auto &explanation : explanations) {
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

TEST_F(TestBoundPreprocessor, ProcessPropagateMultipleOrigins) {
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
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  EXPECT_EQ(bound_preprocessor_.env().size(), 8u);
  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 8u);
  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.cbegin(), ::testing::UnorderedElementsAreArray(active_constraints_));
}

TEST_F(TestBoundPreprocessor, ProcessPropagateMultipleOriginsCommonOrigin) {
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
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  EXPECT_EQ(bound_preprocessor_.env().size(), 9u);
  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 9u);
  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.cbegin(), ::testing::UnorderedElementsAreArray(active_constraints_));
}

TEST_F(TestBoundPreprocessor, ProcessEvaluateViolation) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x2_ == x3_, x3_ == val, x4_ == (x1_ + x5_), x6_ == x2_, x5_ == x6_,
                  x7_ == mpq_class{val + 1}, x7_ == x4_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 7u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], val + 1);
  EXPECT_EQ(bound_preprocessor_.env()[x5_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x6_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x7_], val + 1);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.cbegin(), ::testing::UnorderedElementsAreArray(active_constraints_));
}

TEST_F(TestBoundPreprocessor, ProcessEvaluateViolationInInequalityBound) {
  const mpq_class val = 7;
  AddConstraints({x1_ == val, x1_ == x2_, x2_ == x3_, x3_ > val, x2_ == x4_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], val);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.cbegin(), ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                      active_constraints_[2], active_constraints_[3]));
}

TEST_F(TestBoundPreprocessor, ProcessEvaluateViolationInComplexInequalityBound) {
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
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 4u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], val);
  EXPECT_EQ(bound_preprocessor_.env()[x4_], val);

  ASSERT_THAT(explanations.size(), 3u);
  EXPECT_THAT(*explanations.cbegin(), ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                      active_constraints_[2], active_constraints_[3]));
  EXPECT_THAT(*std::next(explanations.begin()),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[4]));
  EXPECT_THAT(*std::next(std::next(explanations.begin())),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[5]));
}

TEST_F(TestBoundPreprocessor, ProcessBoundSimpleEqBinomial) {
  const mpq_class val = 7;
  const mpq_class lb = (3 * val - 11) / 5;
  const mpq_class ub = (3 * val + 3 - 11) / 5;
  AddConstraints({
      x1_ > val,
      x1_ < mpq_class(val + 1),
      3 * x1_ == 5 * x2_ + 11,
  });
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);
  ASSERT_TRUE(explanations.empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 2u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x1_).active_lower_bound(), val);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x1_).active_upper_bound(), val + 1);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x2_).active_lower_bound(), lb);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x2_).active_upper_bound(), ub);
}
TEST_F(TestBoundPreprocessor, ProcessBoundSimpleGeBinomial) {
  const mpq_class val = 7;
  const mpq_class lb = (3 * val - 11) / 5;
  const mpq_class ub = (3 * val + 3 - 11) / 5;
  AddConstraints({
      x1_ > val,
      x1_ < mpq_class(val + 1),
      3 * x1_ >= 5 * x2_ + 11,
  });
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);
  ASSERT_TRUE(explanations.empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 2u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x1_).active_lower_bound(), val);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x1_).active_upper_bound(), val + 1);
  EXPECT_FALSE(bound_preprocessor_.theory_bounds().at(x2_).IsLowerBounded());
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x2_).active_upper_bound(), ub);
}
TEST_F(TestBoundPreprocessor, ProcessBoundSimpleGtBinomial) {
  const mpq_class val = 7;
  const mpq_class ub = (3 * val + 3 - 11) / 5;
  AddConstraints({
      x1_ > val,
      x1_ < mpq_class(val + 1),
      3 * x1_ > 5 * x2_ + 11,
  });
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);
  ASSERT_TRUE(explanations.empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 2u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x1_).active_lower_bound(), val);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x1_).active_upper_bound(), val + 1);
  EXPECT_FALSE(bound_preprocessor_.theory_bounds().at(x2_).IsLowerBounded());
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x2_).active_upper_bound(), ub);
}
TEST_F(TestBoundPreprocessor, ProcessBoundSimpleLeBinomial) {
  const mpq_class val = 7;
  const mpq_class lb = (3 * val - 11) / 5;
  AddConstraints({
      x1_ > val,
      x1_ < mpq_class(val + 1),
      3 * x1_ <= 5 * x2_ + 11,
  });
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);
  ASSERT_TRUE(explanations.empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 2u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x1_).active_lower_bound(), val);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x1_).active_upper_bound(), val + 1);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x2_).active_lower_bound(), lb);
  EXPECT_FALSE(bound_preprocessor_.theory_bounds().at(x2_).IsUpperBounded());
}
TEST_F(TestBoundPreprocessor, ProcessBoundNegativeLeBinomial) {
  const mpq_class val = 7;
  const mpq_class lb = (3 * val - 11) / 5;
  AddConstraints({
      x1_ > val,
      x1_ < mpq_class(val + 1),
      3 * x1_ <= 5 * x2_ + 11,
  });
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);
  ASSERT_TRUE(explanations.empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 2u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x1_).active_lower_bound(), val);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x1_).active_upper_bound(), val + 1);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x2_).active_lower_bound(), lb);
  EXPECT_FALSE(bound_preprocessor_.theory_bounds().at(x2_).IsUpperBounded());
}

TEST_F(TestBoundPreprocessor, ProcessBoundInferEq) {
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
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.cbegin(),
              ::testing::UnorderedElementsAre(active_constraints_[3], active_constraints_[5], active_constraints_[6],
                                              active_constraints_[10], active_constraints_[11], active_constraints_[12],
                                              active_constraints_[13], active_constraints_[14], active_constraints_[15],
                                              active_constraints_[16]));
}

TEST_F(TestBoundPreprocessor, ProcessBoundLowerBoundMinimalExplanation) {
  AddConstraints({x1_ == x2_, x3_ == x2_, x3_ <= -100, x1_ > -1, x1_ <= 1});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.cbegin(), ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                      active_constraints_[2], active_constraints_[3]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundUpperBoundMinimalExplanation) {
  AddConstraints({x1_ == x2_, x3_ == x2_, x3_ >= 100, x1_ > -1, x1_ <= 1});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.cbegin(), ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                      active_constraints_[2], active_constraints_[4]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundEqBoundMinimalExplanation) {
  AddConstraints({x1_ == x2_, x3_ == x2_, x3_ >= 100, x1_ == 1});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.cbegin(), ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1],
                                                                      active_constraints_[2], active_constraints_[3]));
}

// TODO(tend): support single bounded variables propagation
// TEST_F(TestBoundPreprocessor, ProcessBoundBoundedPropagation) {
//   AddConstraints({x1_ >= 1, x2_ <= 1, x3_ == x1_, x3_ == x2_});
//   const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);
//
//   ASSERT_TRUE(explanations.empty());
//   ASSERT_EQ(bound_preprocessor_.env().size(), 1u);
//   EXPECT_EQ(bound_preprocessor_.env()[x3_], 1);
//
//   ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
//   EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x1_).active_lower_bound(), 1);
//   EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x2_).active_upper_bound(), 1);
//   EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_lower_bound(), 1);
//   EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_upper_bound(), 1);
// }
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedEqPropagationSum) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ == x1_ + x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_TRUE(bound_preprocessor_.env().empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_lower_bound(), -1);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_upper_bound(), 3);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedEqPropagationDifference) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ == x1_ - x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_TRUE(bound_preprocessor_.env().empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_lower_bound(), -3);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_upper_bound(), 1);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedEqPropagationEqualBounds) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, x3_ == x1_ - x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_EQ(bound_preprocessor_.env().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], 1);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], 2);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], -1);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_lower_bound(), -1);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_upper_bound(), -1);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}

TEST_F(TestBoundPreprocessor, ProcessBoundBoundedLePropagationSum) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ <= x1_ + x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_TRUE(bound_preprocessor_.env().empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_upper_bound(), 3);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedLePropagationDifference) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ <= x1_ - x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_TRUE(bound_preprocessor_.env().empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_upper_bound(), 1);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[2], active_constraints_[4]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedLePropagationEqualBounds) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, x3_ <= x1_ - x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_EQ(bound_preprocessor_.env().size(), 2u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], 1);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], 2);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_upper_bound(), -1);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}

TEST_F(TestBoundPreprocessor, ProcessBoundBoundedGePropagationSum) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ >= x1_ + x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_TRUE(bound_preprocessor_.env().empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_lower_bound(), -1);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[2], active_constraints_[4]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedGePropagationDifference) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ >= x1_ - x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_TRUE(bound_preprocessor_.env().empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_lower_bound(), -3);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedGePropagationEqualBounds) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, x3_ >= x1_ - x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_EQ(bound_preprocessor_.env().size(), 2u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], 1);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], 2);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_lower_bound(), -1);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}

TEST_F(TestBoundPreprocessor, ProcessBoundBoundedEqPropagationSumNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ == x1_ + x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_TRUE(bound_preprocessor_.env().empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_lower_bound(), -3);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_upper_bound(), 1);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedEqPropagationDifferenceNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ == x1_ - x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_TRUE(bound_preprocessor_.env().empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_lower_bound(), -1);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_upper_bound(), 3);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedEqPropagationEqualBoundsNegative) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, -x3_ == x1_ - x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_EQ(bound_preprocessor_.env().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], 1);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], 2);
  EXPECT_EQ(bound_preprocessor_.env()[x3_], 1);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_lower_bound(), 1);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_upper_bound(), 1);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}

TEST_F(TestBoundPreprocessor, ProcessBoundBoundedLePropagationSumNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ <= x1_ + x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_TRUE(bound_preprocessor_.env().empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_lower_bound(), -3);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedLePropagationDifferenceNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ <= x1_ - x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_TRUE(bound_preprocessor_.env().empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_lower_bound(), -1);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[2], active_constraints_[4]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedLePropagationEqualBoundsNegative) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, -x3_ <= x1_ - x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_EQ(bound_preprocessor_.env().size(), 2u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], 1);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], 2);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_lower_bound(), 1);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}

TEST_F(TestBoundPreprocessor, ProcessBoundBoundedGePropagationSumNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ >= x1_ + x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_TRUE(bound_preprocessor_.env().empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_upper_bound(), 1);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[2], active_constraints_[4]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedGePropagationDifferenceNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ >= x1_ - x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_TRUE(bound_preprocessor_.env().empty());

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_upper_bound(), 3);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 3u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[3], active_constraints_[4]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedGePropagationEqualBoundsNegative) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, -x3_ >= x1_ - x2_});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_TRUE(explanations.empty());
  ASSERT_EQ(bound_preprocessor_.env().size(), 2u);
  EXPECT_EQ(bound_preprocessor_.env()[x1_], 1);
  EXPECT_EQ(bound_preprocessor_.env()[x2_], 2);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().size(), 3u);
  EXPECT_EQ(bound_preprocessor_.theory_bounds().at(x3_).active_upper_bound(), 1);

  ASSERT_EQ(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation().size(), 5u);
  EXPECT_THAT(bound_preprocessor_.theory_bounds().at(x3_).GetActiveExplanation(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4]));
}

TEST_F(TestBoundPreprocessor, ProcessBoundBoundedEqViolationLowerBound) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ == x1_ + x2_, x3_ >= 4});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.begin(), ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[3],
                                                                     active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedEqViolationUpperBound) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ == x1_ + x2_, x3_ <= -2});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.begin(), ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[2],
                                                                     active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedEqViolationDifferenceUpperBound) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ == x1_ - x2_, x3_ <= -4});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.begin(), ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[3],
                                                                     active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedEqViolationDifferenceLowerBound) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ == x1_ - x2_, x3_ >= 2});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.begin(), ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[2],
                                                                     active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedEqViolationEqLowerBound) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, x3_ == x1_ - x2_, x3_ >= 2});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.begin(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedEqViolationEqUpperBound) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, x3_ == x1_ - x2_, x3_ <= -2});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.begin(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4], active_constraints_[5]));
}

TEST_F(TestBoundPreprocessor, ProcessBoundBoundedLeViolationLower) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ <= x1_ + x2_, x3_ >= 4});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.begin(), ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[3],
                                                                     active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedLeViolationDifference) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, x3_ <= x1_ - x2_, x3_ >= 2});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.begin(), ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[2],
                                                                     active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedLeViolationEqualBounds) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, x3_ <= x1_ - x2_, x3_ >= 0});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.begin(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4], active_constraints_[5]));
}

TEST_F(TestBoundPreprocessor, ProcessBoundBoundedLeViolationLowerNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ <= x1_ + x2_, x3_ <= -100});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.begin(), ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[3],
                                                                     active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedLeViolationDifferenceNegative) {
  AddConstraints({-1 <= x1_, x1_ <= 1, 0 <= x2_, x2_ <= 2, -x3_ <= x1_ - x2_, x3_ <= -100});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.begin(), ::testing::UnorderedElementsAre(active_constraints_[1], active_constraints_[2],
                                                                     active_constraints_[4], active_constraints_[5]));
}
TEST_F(TestBoundPreprocessor, ProcessBoundBoundedLeViolationEqualBoundsNegative) {
  AddConstraints({1 <= x1_, x1_ <= 1, 2 <= x2_, x2_ <= 2, -x3_ <= x1_ - x2_, x3_ <= -100});
  const Explanations explanations = bound_preprocessor_.Process(enabled_literals_);

  ASSERT_EQ(explanations.size(), 1u);
  EXPECT_THAT(*explanations.begin(),
              ::testing::UnorderedElementsAre(active_constraints_[0], active_constraints_[1], active_constraints_[2],
                                              active_constraints_[3], active_constraints_[4], active_constraints_[5]));
}

TEST_F(TestBoundPreprocessor, ShouldPropagateTrue) {
  AddConstraints({x1_ == 0});
  bound_preprocessor_.Process(enabled_literals_);
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(x1_ == x2_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(x1_ == x2_ + x2_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(x2_ + x1_ == x2_ + x2_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(x2_ + x1_ == x2_ + x2_ - x1_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(x1_ + x2_ == 0));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(0 == x1_ + x2_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(2 * x1_ == 3 * x2_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(x1_ - x2_ == 0));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(-x1_ == x2_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(2 * x1_ + 2 * x2_ == 3 * x2_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(x1_ + x2_ == 1));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(x1_ == x2_ + 1));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(1 == x1_ + x2_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(2 * x1_ + 1 == 3 * x2_));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(x1_ - x2_ == 1));
  EXPECT_TRUE(bound_preprocessor_.ShouldPropagate(-x1_ == x2_ - 1));
}

TEST_F(TestBoundPreprocessor, ShouldPropagateFalse) {
  AddConstraints({x1_ == 0});
  bound_preprocessor_.Process(enabled_literals_);
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(x1_ == 0));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(0 == x2_));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(x1_ == x2_ + x3_));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(x1_ + x3_ == x2_));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(2 * x1_ + 3 * x2_ == 3 * x2_));
  EXPECT_FALSE(bound_preprocessor_.ShouldPropagate(x2_ + x1_ == x2_ + x2_ + x1_));
}

TEST_F(TestBoundPreprocessor, ExtractCoefficient) {
  EXPECT_EQ(bound_preprocessor_.ExtractCoefficient(x1_ == x2_), 1);
  EXPECT_EQ(bound_preprocessor_.ExtractCoefficient(x1_ + x2_ == 0), -1);
  EXPECT_EQ(bound_preprocessor_.ExtractCoefficient(2 * x1_ == 3 * x2_), mpq_class(3, 2));
  EXPECT_EQ(bound_preprocessor_.ExtractCoefficient(x1_ - x2_ == 0), 1);
  EXPECT_EQ(bound_preprocessor_.ExtractCoefficient(-x1_ == x2_), -1);
  EXPECT_EQ(bound_preprocessor_.ExtractCoefficient(x1_ + x2_ == 0), -1);
  EXPECT_EQ(bound_preprocessor_.ExtractCoefficient(0 == x1_ + x2_), -1);
  EXPECT_EQ(bound_preprocessor_.ExtractCoefficient(x2_ + x1_ == x2_ + x2_), 1);
  EXPECT_EQ(bound_preprocessor_.ExtractCoefficient(x2_ + x1_ == x2_ + x2_ - x1_), mpq_class(1, 2));
  EXPECT_EQ(bound_preprocessor_.ExtractCoefficient(2 * x1_ + 2 * x2_ == 3 * x2_), mpq_class(1, 2));
}

TEST_F(TestBoundPreprocessor, Stdcout) { EXPECT_NO_THROW(std::cout << bound_preprocessor_ << std::endl); }
