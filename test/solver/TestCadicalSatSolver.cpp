/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <memory>

#include "dlinear/solver/CadicalSatSolver.h"

using dlinear::CadicalSatSolver;
using dlinear::Config;
using dlinear::Formula;
using dlinear::iff;
using dlinear::imply;
using dlinear::Literal;
using dlinear::LiteralSet;
using dlinear::Model;
using dlinear::PredicateAbstractor;
using dlinear::SatSolver;
using dlinear::Variable;
using std::unique_ptr;

class TestCadicalSatSolver : public ::testing::Test {
 protected:
  const Config config_;
  PredicateAbstractor pa_;
  const Variable x_{"x"}, y_{"y"};
  const Formula f_{x_ > 1};
  const Formula f2_{!(y_ > 2)};
  const Formula f3_{x_ + y_ <= 3};
  const Formula f4_{f_ || f2_ || f3_};
  const Variable bx_{"bx", Variable::Type::BOOLEAN};
  const Variable by_{"by", Variable::Type::BOOLEAN};
  const Variable bz_{"bz", Variable::Type::BOOLEAN};
  CadicalSatSolver s_;
  explicit TestCadicalSatSolver() : config_{get_config()}, pa_{config_}, s_{pa_} {}

  static Config get_config() {
    Config config{};
    config.m_filename() = "test.smt2";
    config.m_format() = Config::Format::AUTO;
    return config;
  }
};

bool TrueLiteral(const Literal& l) { return l.truth; }
bool FalseLiteral(const Literal& l) { return !l.truth; }

TEST_F(TestCadicalSatSolver, Constructor) { CadicalSatSolver s{pa_}; }

TEST_F(TestCadicalSatSolver, AddFormula) {
  s_.AddFormula(f_);

  EXPECT_EQ(pa_.var_to_formula_map().size(), 1u);
}

TEST_F(TestCadicalSatSolver, AddClauseLiteral) {
  s_.AddClause(Formula{Variable{"x_", Variable::Type::BOOLEAN}});

  EXPECT_EQ(pa_.var_to_formula_map().size(), 0u);
}

TEST_F(TestCadicalSatSolver, AddClauseDisjunction) {
  s_.AddClause(bx_ || by_);

  EXPECT_EQ(pa_.var_to_formula_map().size(), 0u);
}

TEST_F(TestCadicalSatSolver, SingleTrueValue) {
  s_.AddFormula(Formula{bx_});

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_EQ(res.value().first.size(), 1u);
  EXPECT_TRUE(std::all_of(res.value().first.begin(), res.value().first.end(), TrueLiteral));
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestCadicalSatSolver, SingleFalseValue) {
  s_.AddFormula(!bx_);

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_EQ(res.value().first.size(), 1u);
  EXPECT_TRUE(std::none_of(res.value().first.begin(), res.value().first.end(), TrueLiteral));
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestCadicalSatSolver, SolveOrTwo) {
  s_.AddFormula(bx_ || by_);

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_LE(res.value().first.size(), 2u);
  EXPECT_GE(std::count_if(res.value().first.begin(), res.value().first.end(), TrueLiteral), 1);
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestCadicalSatSolver, SolveOrThree) {
  s_.AddFormula(bx_ || by_ || bz_);

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_LE(res.value().first.size(), 3u);
  EXPECT_GE(std::count_if(res.value().first.begin(), res.value().first.end(), TrueLiteral), 1);
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestCadicalSatSolver, SolveAndTwo) {
  s_.AddFormula(bx_ && by_);

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());

  EXPECT_EQ(res.value().first.size(), 2u);
  EXPECT_EQ(std::count_if(res.value().first.begin(), res.value().first.end(), TrueLiteral), 2);
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestCadicalSatSolver, SolveAndThree) {
  s_.AddFormula(bx_ && by_ && bz_);

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_EQ(res.value().first.size(), 3u);
  EXPECT_EQ(std::count_if(res.value().first.begin(), res.value().first.end(), TrueLiteral), 3);
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestCadicalSatSolver, SolveImplyFalse) {
  s_.AddFormula(imply(bx_, by_));
  s_.AddFormula(!by_);

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_EQ(res.value().first.size(), 2u);
  EXPECT_TRUE(std::all_of(res.value().first.begin(), res.value().first.end(), FalseLiteral));
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestCadicalSatSolver, SolveImplyTrue) {
  s_.AddFormula(imply(bx_, by_));
  s_.AddFormula(Formula{bx_});

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_EQ(res.value().first.size(), 2u);
  EXPECT_TRUE(std::all_of(res.value().first.begin(), res.value().first.end(), TrueLiteral));
  EXPECT_TRUE(res.value().second.empty());
}
TEST_F(TestCadicalSatSolver, SolveIffFalse) {
  s_.AddFormula(iff(bx_, by_));
  s_.AddFormula(!bx_);

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_EQ(res.value().first.size(), 2u);
  EXPECT_TRUE(std::all_of(res.value().first.begin(), res.value().first.end(), FalseLiteral));
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestCadicalSatSolver, SolveIffTrue) {
  s_.AddFormula(iff(bx_, by_));
  s_.AddFormula(Formula{bx_});

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_EQ(res.value().first.size(), 2u);
  EXPECT_TRUE(std::all_of(res.value().first.begin(), res.value().first.end(), TrueLiteral));
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestCadicalSatSolver, FixedSingleTrue) {
  s_.AddFormula(x_ > 0);
  s_.AddFormula(x_ != 1);
  s_.AddFormula(x_ == 2);
  s_.AddFormula(x_ <= 3);
  s_.AddFormula(Formula{bx_});

  const LiteralSet fixed_literals = s_.dlinear::SatSolver::FixedTheoryLiterals();
  EXPECT_THAT(fixed_literals, ::testing::UnorderedElementsAre(Literal{s_.predicate_abstractor()[x_ <= 0], false},
                                                              Literal{s_.predicate_abstractor()[x_ == 1], false},
                                                              Literal{s_.predicate_abstractor()[x_ == 2], true},
                                                              Literal{s_.predicate_abstractor()[x_ <= 3], true}));
}

TEST_F(TestCadicalSatSolver, FixedSingleFalse) {
  s_.AddFormula(!(x_ > 0));
  s_.AddFormula(!(x_ != 1));
  s_.AddFormula(!(x_ == 2));
  s_.AddFormula(!(x_ <= 3));
  s_.AddFormula(!Formula{bx_});

  const LiteralSet fixed_literals = s_.FixedTheoryLiterals();
  EXPECT_THAT(fixed_literals, ::testing::UnorderedElementsAre(Literal{s_.predicate_abstractor()[x_ <= 0], true},
                                                              Literal{s_.predicate_abstractor()[x_ == 1], true},
                                                              Literal{s_.predicate_abstractor()[x_ == 2], false},
                                                              Literal{s_.predicate_abstractor()[x_ <= 3], false}));
}

TEST_F(TestCadicalSatSolver, FixedAnd) {
  s_.AddFormula((x_ < 0) && (y_ < 0));
  s_.AddFormula(bx_ && by_);

  const LiteralSet fixed_literals = s_.FixedTheoryLiterals();
  EXPECT_THAT(fixed_literals, ::testing::UnorderedElementsAre(Literal{s_.predicate_abstractor()[x_ < 0], true},
                                                              Literal{s_.predicate_abstractor()[y_ < 0], true}));
}

TEST_F(TestCadicalSatSolver, FixedOr) {
  s_.AddFormula((x_ < 0) || (y_ < 0));
  s_.AddFormula(bx_ || by_);

  const LiteralSet fixed_literals = s_.FixedTheoryLiterals();
  EXPECT_TRUE(fixed_literals.empty());
}

TEST_F(TestCadicalSatSolver, Assume) {
  s_.AddFormula((x_ < 0) || (y_ < 0));
  s_.Assume({s_.predicate_abstractor()[x_ < 0], false});
  const auto [bool_model, theory_model] = s_.CheckSat().value();

  EXPECT_TRUE(bool_model.empty());
  ASSERT_EQ(theory_model.size(), 1u);
  EXPECT_THAT(theory_model, ::testing::UnorderedElementsAre(Literal{s_.predicate_abstractor()[y_ < 0], true}));

  s_.Assume({s_.predicate_abstractor()[y_ < 0], false});
  const auto [bool_model2, theory_model2] = s_.CheckSat().value();

  EXPECT_TRUE(bool_model2.empty());
  ASSERT_EQ(theory_model2.size(), 1u);
  EXPECT_THAT(theory_model2, ::testing::UnorderedElementsAre(Literal{s_.predicate_abstractor()[x_ < 0], true}));

  s_.Assume({s_.predicate_abstractor()[x_ < 0], true});
  s_.Assume({s_.predicate_abstractor()[y_ < 0], true});
  const auto [bool_model3, theory_model3] = s_.CheckSat().value();

  EXPECT_TRUE(bool_model3.empty());
  ASSERT_EQ(theory_model3.size(), 1u);
  EXPECT_THAT(theory_model3, ::testing::UnorderedElementsAre(Literal{s_.predicate_abstractor()[y_ < 0], true}));
}
