/**
 * @file TestPicosatSatSolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include <functional>
#include <memory>

#include "dlinear/solver/PicosatSatSolver.h"

using dlinear::Config;
using dlinear::Formula;
using dlinear::iff;
using dlinear::imply;
using dlinear::Literal;
using dlinear::Model;
using dlinear::PicosatSatSolver;
using dlinear::PredicateAbstractor;
using dlinear::SatSolver;
using dlinear::Variable;
using std::unique_ptr;

class TestPicosatSatSolver : public ::testing::Test {
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
  PicosatSatSolver s_;
  explicit TestPicosatSatSolver() : config_{get_config()}, pa_{config_}, s_{pa_} {}

  static Config get_config() {
    Config config{};
    config.m_filename() = "test.smt2";
    config.m_format() = Config::Format::AUTO;
    return config;
  }
};

bool TrueLiteral(const Literal& l) { return l.truth; }
bool FalseLiteral(const Literal& l) { return !l.truth; }

TEST_F(TestPicosatSatSolver, Constructor) { PicosatSatSolver s{pa_}; }

TEST_F(TestPicosatSatSolver, AddFormula) {
  s_.AddFormula(f_);

  EXPECT_EQ(pa_.var_to_formula_map().size(), 1u);
}

TEST_F(TestPicosatSatSolver, AddClauseLiteral) {
  s_.AddClause(Formula{bx_});

  EXPECT_EQ(pa_.var_to_formula_map().size(), 0u);
}

TEST_F(TestPicosatSatSolver, AddClauseDisjunction) {
  s_.AddClause(bx_ || by_);

  EXPECT_EQ(pa_.var_to_formula_map().size(), 0u);
}

TEST_F(TestPicosatSatSolver, SingleTrueValue) {
  s_.AddFormula(Formula{bx_});

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_EQ(res.value().first.size(), 1u);
  EXPECT_TRUE(std::all_of(res.value().first.begin(), res.value().first.end(), TrueLiteral));
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestPicosatSatSolver, SingleFalseValue) {
  s_.AddFormula(!bx_);

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_EQ(res.value().first.size(), 1u);
  EXPECT_TRUE(std::none_of(res.value().first.begin(), res.value().first.end(), TrueLiteral));
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestPicosatSatSolver, SolveOrTwo) {
  s_.AddFormula(bx_ || by_);

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_LE(res.value().first.size(), 2u);
  EXPECT_GE(std::count_if(res.value().first.begin(), res.value().first.end(), TrueLiteral), 1);
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestPicosatSatSolver, SolveOrThree) {
  s_.AddFormula(bx_ || by_ || bz_);

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_LE(res.value().first.size(), 3u);
  EXPECT_GE(std::count_if(res.value().first.begin(), res.value().first.end(), TrueLiteral), 1);
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestPicosatSatSolver, SolveAndTwo) {
  s_.AddFormula(bx_ && by_);

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_EQ(res.value().first.size(), 2u);
  EXPECT_EQ(std::count_if(res.value().first.begin(), res.value().first.end(), TrueLiteral), 2);
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestPicosatSatSolver, SolveAndThree) {
  s_.AddFormula(bx_ && by_ && bz_);

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_EQ(res.value().first.size(), 3u);
  EXPECT_EQ(std::count_if(res.value().first.begin(), res.value().first.end(), TrueLiteral), 3);
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestPicosatSatSolver, SolveImplyFalse) {
  s_.AddFormula(imply(bx_, by_));
  s_.AddFormula(!by_);

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_EQ(res.value().first.size(), 2u);
  EXPECT_TRUE(std::all_of(res.value().first.begin(), res.value().first.end(), FalseLiteral));
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestPicosatSatSolver, SolveImplyTrue) {
  s_.AddFormula(imply(bx_, by_));
  s_.AddFormula(Formula{bx_});

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_EQ(res.value().first.size(), 2u);
  EXPECT_TRUE(std::all_of(res.value().first.begin(), res.value().first.end(), TrueLiteral));
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestPicosatSatSolver, SolveIffFalse) {
  s_.AddFormula(iff(bx_, by_));
  s_.AddFormula(!bx_);

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_EQ(res.value().first.size(), 2u);
  EXPECT_TRUE(std::all_of(res.value().first.begin(), res.value().first.end(), FalseLiteral));
  EXPECT_TRUE(res.value().second.empty());
}

TEST_F(TestPicosatSatSolver, SolveIffTrue) {
  s_.AddFormula(iff(bx_, by_));
  s_.AddFormula(Formula{bx_});

  const std::optional<Model> res = s_.CheckSat();
  EXPECT_TRUE(res.has_value());
  EXPECT_EQ(res.value().first.size(), 2u);
  EXPECT_TRUE(std::all_of(res.value().first.begin(), res.value().first.end(), TrueLiteral));
  EXPECT_TRUE(res.value().second.empty());
}
