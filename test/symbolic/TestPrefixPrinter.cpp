/**
 * @file TestPrefixPrinter.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "dlinear/symbolic/PrefixPrinter.h"
#include "TestSymbolicUtils.h"

#include <gtest/gtest.h>

using dlinear::ToPrefix;

class TestPrefixPrinter : public ::testing::Test {
 protected:
  const Variable x_{"x", Variable::Type::CONTINUOUS};
  const Variable y_{"y", Variable::Type::CONTINUOUS};
  const Variable z_{"z", Variable::Type::CONTINUOUS};

  const Variable i1_{"i1", Variable::Type::INTEGER};
  const Variable i2_{"i2", Variable::Type::INTEGER};
  const Variable i3_{"i3", Variable::Type::INTEGER};

  const Variable b1_{"b1", Variable::Type::BOOLEAN};
  const Variable b2_{"b2", Variable::Type::BOOLEAN};
  const Variable b3_{"b3", Variable::Type::BOOLEAN};
};

TEST_F(TestPrefixPrinter, Variable) {
  const Expression e{x_};
  EXPECT_EQ(ToPrefix(e), "x");
}

TEST_F(TestPrefixPrinter, Constant1) {
  const Expression e{3};
  EXPECT_EQ(ToPrefix(e), "3");
}

TEST_F(TestPrefixPrinter, Constant2) {
  const Expression e{mpq_class(M_PI)};
  EXPECT_EQ(ToPrefix(e), "(/ 884279719003555 281474976710656)");
}

TEST_F(TestPrefixPrinter, Addition) {
  const Expression e{x_ + 2 * y_ + 3 * z_};
  EXPECT_EQ(ToPrefix(e), "(+ x (* 2 y) (* 3 z))");
}

TEST_F(TestPrefixPrinter, Multiplication) {
  const Expression e{pow(x_, 2) * 2 * y_ * 3 * pow(z_, 5)};
  EXPECT_EQ(ToPrefix(e), "(* 6 (^ x 2) y (^ z 5))");
}

TEST_F(TestPrefixPrinter, Division) {
  const Expression e{x_ / y_};
  EXPECT_EQ(ToPrefix(e), "(/ x y)");
}

TEST_F(TestPrefixPrinter, Log) {
  const Expression e{log(x_)};
  EXPECT_EQ(ToPrefix(e), "(log x)");
}

TEST_F(TestPrefixPrinter, Abs) {
  const Expression e{abs(x_)};
  EXPECT_EQ(ToPrefix(e), "(abs x)");
}

TEST_F(TestPrefixPrinter, Exp) {
  const Expression e{exp(x_)};
  EXPECT_EQ(ToPrefix(e), "(exp x)");
}

TEST_F(TestPrefixPrinter, Sqrt) {
  const Expression e{sqrt(x_)};
  EXPECT_EQ(ToPrefix(e), "(sqrt x)");
}

TEST_F(TestPrefixPrinter, Pow) {
  const Expression e{pow(x_, y_)};
  EXPECT_EQ(ToPrefix(e), "(^ x y)");
}

TEST_F(TestPrefixPrinter, Sin) {
  const Expression e{sin(x_)};
  EXPECT_EQ(ToPrefix(e), "(sin x)");
}

TEST_F(TestPrefixPrinter, Cos) {
  const Expression e{cos(x_)};
  EXPECT_EQ(ToPrefix(e), "(cos x)");
}

TEST_F(TestPrefixPrinter, Tan) {
  const Expression e{tan(x_)};
  EXPECT_EQ(ToPrefix(e), "(tan x)");
}

TEST_F(TestPrefixPrinter, Asin) {
  const Expression e{asin(x_)};
  EXPECT_EQ(ToPrefix(e), "(asin x)");
}

TEST_F(TestPrefixPrinter, Acos) {
  const Expression e{acos(x_)};
  EXPECT_EQ(ToPrefix(e), "(acos x)");
}

TEST_F(TestPrefixPrinter, Atan) {
  const Expression e{atan(x_)};
  EXPECT_EQ(ToPrefix(e), "(atan x)");
}

TEST_F(TestPrefixPrinter, Atan2) {
  const Expression e{atan2(x_, y_)};
  EXPECT_EQ(ToPrefix(e), "(atan2 x y)");
}

TEST_F(TestPrefixPrinter, Sinh) {
  const Expression e{sinh(x_)};
  EXPECT_EQ(ToPrefix(e), "(sinh x)");
}

TEST_F(TestPrefixPrinter, Cosh) {
  const Expression e{cosh(x_)};
  EXPECT_EQ(ToPrefix(e), "(cosh x)");
}

TEST_F(TestPrefixPrinter, Tanh) {
  const Expression e{tanh(x_)};
  EXPECT_EQ(ToPrefix(e), "(tanh x)");
}

TEST_F(TestPrefixPrinter, Min) {
  const Expression e{min(x_, y_)};
  EXPECT_EQ(ToPrefix(e), "(min x y)");
}

TEST_F(TestPrefixPrinter, Max) {
  const Expression e{max(x_, y_)};
  EXPECT_EQ(ToPrefix(e), "(max x y)");
}

TEST_F(TestPrefixPrinter, IfThenElse) {
  const Expression e{if_then_else(x_ > y_, x_, y_)};
  EXPECT_EQ(ToPrefix(e), "(ite (> x y) x y)");
}

TEST_F(TestPrefixPrinter, False) { EXPECT_EQ(ToPrefix(x_ != x_), "false"); }

TEST_F(TestPrefixPrinter, True) { EXPECT_EQ(ToPrefix(x_ == x_), "true"); }

TEST_F(TestPrefixPrinter, FormulaVariable) {
  EXPECT_EQ(ToPrefix(Formula{b1_}), "b1");
}

TEST_F(TestPrefixPrinter, EqualTo) { EXPECT_EQ(ToPrefix(x_ == y_), "(= x y)"); }

TEST_F(TestPrefixPrinter, NotEqualTo) {
  EXPECT_EQ(ToPrefix(x_ != y_), "(not (= x y))");
}

TEST_F(TestPrefixPrinter, GT) { EXPECT_EQ(ToPrefix(x_ > y_), "(> x y)"); }

TEST_F(TestPrefixPrinter, GTE) { EXPECT_EQ(ToPrefix(x_ >= y_), "(>= x y)"); }

TEST_F(TestPrefixPrinter, LT) { EXPECT_EQ(ToPrefix(x_ < y_), "(< x y)"); }

TEST_F(TestPrefixPrinter, LTE) { EXPECT_EQ(ToPrefix(x_ <= y_), "(<= x y)"); }

TEST_F(TestPrefixPrinter, And) {
  EXPECT_EQ(ToPrefix(x_ <= y_ && y_ <= z_ && z_ <= x_),
            "(and (<= x y) (<= y z) (<= z x))");
}

TEST_F(TestPrefixPrinter, Or) {
  EXPECT_EQ(ToPrefix(x_ <= y_ || y_ <= z_ || z_ <= x_),
            "(or (<= x y) (<= y z) (<= z x))");
}

TEST_F(TestPrefixPrinter, Negation) {
  EXPECT_EQ(ToPrefix(!(x_ <= y_)), "(not (<= x y))");
}