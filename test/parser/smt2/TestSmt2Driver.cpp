/**
 * @file TestSmt2Driver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include "dlinear/parser/smt2/Driver.h"
#include "test/symbolic/TestSymbolicUtils.h"

using dlinear::Config;
using dlinear::Context;
using dlinear::Variable;
using dlinear::smt2::FunctionDefinition;
using dlinear::smt2::Smt2Driver;
using dlinear::smt2::Term;

class TestSmt2Driver : public ::testing::Test {
 protected:
  Config config_;
  Context context_{config_};
};

TEST_F(TestSmt2Driver, ValidSetLogic) {
  Smt2Driver driver{context_};
  EXPECT_TRUE(driver.ParseString("(set-logic QF_LRA)"));
}

TEST_F(TestSmt2Driver, InvalidSetLogic) {
  Smt2Driver driver{context_};
  EXPECT_THROW(driver.ParseString("(set-logic QF_LIA)"), std::runtime_error);
  EXPECT_THROW(driver.ParseString("(set-logic LRA)"), std::runtime_error);
  EXPECT_THROW(driver.ParseString("(set-logic LIA)"), std::runtime_error);
  EXPECT_THROW(driver.ParseString("(set-logic QF_BV)"), std::runtime_error);
  EXPECT_THROW(driver.ParseString("(set-logic QF_UF)"), std::runtime_error);
  EXPECT_THROW(driver.ParseString("(set-logic QF_UFBV)"), std::runtime_error);
}

TEST_F(TestSmt2Driver, DeclareVariables) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(declare-fun r () Real)\n"
                         "; (declare-fun i () Int)\n"  // Integer is not supported
                         "(declare-fun b () Bool)\n"
                         "; (declare-fun bin () Binary)"));  // Binary is not supported

  const Variable& r = driver.LookupVariable("r");
  //  const Variable& i = driver.LookupVariable("i");
  const Variable& b = driver.LookupVariable("b");
  //  const Variable& bin = driver.LookupVariable("bin");

  EXPECT_EQ(r.get_name(), "r");
  EXPECT_EQ(r.get_type(), Variable::Type::CONTINUOUS);
  //  EXPECT_EQ(i.get_name(), "i");
  //  EXPECT_EQ(i.get_type(), Variable::Type::INTEGER);
  EXPECT_EQ(b.get_name(), "b");
  EXPECT_EQ(b.get_type(), Variable::Type::BOOLEAN);
  //  EXPECT_EQ(bin.get_name(), "bin");
  //  EXPECT_EQ(bin.get_type(), Variable::Type::BINARY);

  EXPECT_EQ(driver.context().box().size(), 2);
}

TEST_F(TestSmt2Driver, DeclareSort) {
  Smt2Driver driver{context_};
  EXPECT_THROW(driver.ParseString("(declare-sort A 0)"), std::runtime_error);
}

TEST_F(TestSmt2Driver, DefineSortAlias) {
  Smt2Driver driver{context_};
  EXPECT_THROW(driver.ParseString("(define-sort I () Int)"), std::runtime_error);
}

TEST_F(TestSmt2Driver, DefineSortParameters) {
  Smt2Driver driver{context_};
  EXPECT_THROW(driver.ParseString("(define-sort P (X) (Pair X X))"), std::runtime_error);
}

TEST_F(TestSmt2Driver, GetProof) {
  Smt2Driver driver{context_};
  EXPECT_THROW(driver.ParseString("(get-proof)"), std::runtime_error);
}

TEST_F(TestSmt2Driver, GetUnsatCore) {
  Smt2Driver driver{context_};
  EXPECT_THROW(driver.ParseString("(get-unsat-core)"), std::runtime_error);
}

TEST_F(TestSmt2Driver, SimpleRealAssertion) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(declare-fun lhs () Real)\n"
                         "(declare-fun rhs () Real)\n"
                         "(assert (>= lhs rhs))"));

  const Variable& lhs = driver.LookupVariable("lhs");
  const Variable& rhs = driver.LookupVariable("rhs");
  EXPECT_EQ(lhs.get_name(), "lhs");
  EXPECT_EQ(lhs.get_type(), Variable::Type::CONTINUOUS);
  EXPECT_EQ(rhs.get_name(), "rhs");
  EXPECT_EQ(rhs.get_type(), Variable::Type::CONTINUOUS);

  EXPECT_EQ(driver.context().box().size(), 2);
  EXPECT_EQ(driver.context().assertions().size(), 1u);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(lhs >= rhs));
}

TEST_F(TestSmt2Driver, NegatedRealAssertion) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(declare-fun lhs () Real)\n"
                         "(declare-fun rhs () Real)\n"
                         "(assert (not (>= lhs rhs)))"));

  const Variable& lhs = driver.LookupVariable("lhs");
  const Variable& rhs = driver.LookupVariable("rhs");
  EXPECT_EQ(lhs.get_name(), "lhs");
  EXPECT_EQ(lhs.get_type(), Variable::Type::CONTINUOUS);
  EXPECT_EQ(rhs.get_name(), "rhs");
  EXPECT_EQ(rhs.get_type(), Variable::Type::CONTINUOUS);

  EXPECT_EQ(driver.context().box().size(), 2);
  EXPECT_EQ(driver.context().assertions().size(), 1u);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(!(lhs >= rhs)));
}

TEST_F(TestSmt2Driver, SimpleBoolAssertion) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(declare-fun lhs () Bool)\n"
                         "(declare-fun rhs () Bool)\n"
                         "(assert (= lhs rhs))"));

  const Variable& lhs = driver.LookupVariable("lhs");
  const Variable& rhs = driver.LookupVariable("rhs");
  EXPECT_EQ(lhs.get_name(), "lhs");
  EXPECT_EQ(lhs.get_type(), Variable::Type::BOOLEAN);
  EXPECT_EQ(rhs.get_name(), "rhs");
  EXPECT_EQ(rhs.get_type(), Variable::Type::BOOLEAN);

  EXPECT_EQ(driver.context().box().size(), 2);
  EXPECT_EQ(driver.context().assertions().size(), 1u);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(lhs == rhs));
}

TEST_F(TestSmt2Driver, NegatedBoolAssertion) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(declare-fun lhs () Bool)\n"
                         "(declare-fun rhs () Bool)\n"
                         "(assert (not (= lhs rhs)))"));

  const Variable& lhs = driver.LookupVariable("lhs");
  const Variable& rhs = driver.LookupVariable("rhs");
  EXPECT_EQ(lhs.get_name(), "lhs");
  EXPECT_EQ(lhs.get_type(), Variable::Type::BOOLEAN);
  EXPECT_EQ(rhs.get_name(), "rhs");
  EXPECT_EQ(rhs.get_type(), Variable::Type::BOOLEAN);

  EXPECT_EQ(driver.context().box().size(), 2);
  EXPECT_EQ(driver.context().assertions().size(), 1u);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(lhs != rhs));
}

TEST_F(TestSmt2Driver, LetCommand) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(declare-fun x () Real)\n"
                         "(declare-fun y () Real)\n"
                         "(assert (let ((lhs x) (rhs y)) (= lhs rhs)))"));

  const Variable& x = driver.LookupVariable("x");
  const Variable& y = driver.LookupVariable("y");
  EXPECT_THROW(Variable lhs = driver.LookupVariable("lhs"), std::out_of_range);
  EXPECT_THROW(Variable rhs = driver.LookupVariable("rhs"), std::out_of_range);

  EXPECT_EQ(driver.context().box().size(), 4);
  EXPECT_EQ(driver.context().assertions().size(), 3u);

  const Variable& lhs = driver.context().box().variable(3);
  const Variable& rhs = driver.context().box().variable(2);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(rhs == y));
  EXPECT_TRUE(driver.context().assertions()[1].EqualTo(lhs == x));
  EXPECT_TRUE(driver.context().assertions()[2].EqualTo(lhs == rhs));
}

TEST_F(TestSmt2Driver, LetConstantCommand) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(declare-fun x () Real)\n"
                         "(declare-fun y () Real)\n"
                         "(assert (let ((lhs x) (rhs y) (c 42)) (= (+ lhs rhs) c)))\n"
                         "(assert (let ((lhs y) (rhs x) (c 12)) (= (+ lhs rhs) 12)))"));

  const Variable& x = driver.LookupVariable("x");
  const Variable& y = driver.LookupVariable("y");
  EXPECT_THROW(Variable lhs = driver.LookupVariable("lhs"), std::out_of_range);
  EXPECT_THROW(Variable rhs = driver.LookupVariable("rhs"), std::out_of_range);

  EXPECT_EQ(driver.context().box().size(), 6);
  EXPECT_EQ(driver.context().assertions().size(), 6u);

  const Variable& lhs1 = driver.context().box().variable(3);
  const Variable& rhs1 = driver.context().box().variable(2);
  const Variable& lhs2 = driver.context().box().variable(5);
  const Variable& rhs2 = driver.context().box().variable(4);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(rhs1 == y));
  EXPECT_TRUE(driver.context().assertions()[1].EqualTo(lhs1 == x));
  EXPECT_TRUE(driver.context().assertions()[2].EqualTo((lhs1 + rhs1 == 42)));
  EXPECT_TRUE(driver.context().assertions()[3].EqualTo(rhs2 == x));
  EXPECT_TRUE(driver.context().assertions()[4].EqualTo(lhs2 == y));
  EXPECT_TRUE(driver.context().assertions()[5].EqualTo((lhs2 + rhs2 == 12)));
}

TEST_F(TestSmt2Driver, CustomSumFunction) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(declare-fun x () Real)\n"
                         "(declare-fun y () Real)\n"
                         "(define-fun sum ((a Real) (b Real)) Real (+ a b))\n"
                         "(assert (= (sum x y) (* x 2)))"));

  const Variable& x = driver.LookupVariable("x");
  const Variable& y = driver.LookupVariable("y");
  const Term sum = driver.LookupFunction("sum", {Term{x}, Term{y}});
  EXPECT_TRUE(sum.expression().EqualTo(x + y));

  EXPECT_EQ(driver.context().box().size(), 4);
  EXPECT_EQ(driver.context().assertions().size(), 1u);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(x + y == 2 * x));
}

TEST_F(TestSmt2Driver, IgnoreRedefinedMaxFunction) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(declare-fun x () Real)\n"
                         "(declare-fun y () Real)\n"
                         "(define-fun max ((a Real) (b Real)) Real (+ a b))\n"
                         "(assert (<= x 0))\n"
                         "(assert (<= y 1))\n"
                         "(assert (= (max x y) 1))"));

  const Variable& x = driver.LookupVariable("x");
  const Variable& y = driver.LookupVariable("y");
  EXPECT_THROW(driver.LookupFunction("max", {Term{x}, Term{y}}), std::out_of_range);

  EXPECT_EQ(driver.context().box().size(), 4);
  EXPECT_EQ(driver.context().assertions().size(), 3u);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(x <= 0));
  EXPECT_TRUE(driver.context().assertions()[1].EqualTo(y <= 1));
  EXPECT_TRUE(driver.context().assertions()[2].EqualTo(max(x, y) == 1));
}

TEST_F(TestSmt2Driver, IgnoreRedefinedMinFunction) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(declare-fun x () Real)\n"
                         "(declare-fun y () Real)\n"
                         "(define-fun min ((a Real) (b Real)) Real (+ a b))\n"
                         "(assert (<= x 0))\n"
                         "(assert (<= y 1))\n"
                         "(assert (= (min x y) 1))"));

  const Variable& x = driver.LookupVariable("x");
  const Variable& y = driver.LookupVariable("y");
  EXPECT_THROW(driver.LookupFunction("max", {Term{x}, Term{y}}), std::out_of_range);

  EXPECT_EQ(driver.context().box().size(), 4);
  EXPECT_EQ(driver.context().assertions().size(), 3u);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(x <= 0));
  EXPECT_TRUE(driver.context().assertions()[1].EqualTo(y <= 1));
  EXPECT_TRUE(driver.context().assertions()[2].EqualTo(min(x, y) == 1));
}

TEST_F(TestSmt2Driver, EmptyGetAssertions) {
  Smt2Driver driver{context_};
  EXPECT_TRUE(driver.ParseString("(get-assertions)"));
  EXPECT_TRUE(driver.context().assertions().empty());
}

TEST_F(TestSmt2Driver, GetAssertions) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(declare-fun x () Real)\n"
                         "(declare-fun y () Real)\n"
                         "(assert (let ((lhs x) (rhs y) (c 42)) (= (+ lhs rhs) c)))\n"
                         "(get-assertions)"));
  EXPECT_FALSE(driver.context().assertions().empty());
}

TEST_F(TestSmt2Driver, EmptyGetModel) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(assert (= 1 2))\n"
                         "(check-sat)\n"
                         "(get-model)"));
  EXPECT_TRUE(driver.context().model().empty());
}

TEST_F(TestSmt2Driver, GetModel) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(declare-fun x () Real)\n"
                         "(declare-fun y () Real)\n"
                         "(assert (let ((lhs x) (rhs y) (c 42)) (= (+ lhs rhs) c)))\n"
                         "(check-sat)"
                         "(get-assertions)"));
  EXPECT_FALSE(driver.context().model().empty());
}

TEST_F(TestSmt2Driver, EmptyGetAssignment) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(assert (= 1 2))\n"
                         "(check-sat)\n"
                         "(get-assignment)"));
  EXPECT_TRUE(driver.context().model().empty());
}

TEST_F(TestSmt2Driver, GetAssignment) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(declare-fun x () Real)\n"
                         "(declare-fun y () Real)\n"
                         "(assert (let ((lhs x) (rhs y) (c 42)) (= (+ lhs rhs) c)))\n"
                         "(check-sat)"
                         "(get-assignment)"));
  EXPECT_FALSE(driver.context().model().empty());
}

TEST_F(TestSmt2Driver, SetConfigOptions1) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(set-option :precision 1)\n"
                         "(set-option :produce-models true)\n"));
  EXPECT_EQ(driver.context().config().precision(), 1);
  EXPECT_TRUE(driver.context().config().produce_models());
}

TEST_F(TestSmt2Driver, SetConfigOptions2) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(set-option :precision 0.505)\n"
                         "(set-option :produce-models false)\n"));
  EXPECT_EQ(driver.context().config().precision(), 0.505);
  EXPECT_FALSE(driver.context().config().produce_models());
}

TEST_F(TestSmt2Driver, EmptyGetOption) {
  Smt2Driver driver{context_};
  EXPECT_TRUE(driver.ParseString("(get-option :produce-models)"));
}

TEST_F(TestSmt2Driver, GetOption) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(set-option :produce-models true)\n"
                         "(get-option :produce-models)"));
}

TEST_F(TestSmt2Driver, EmptyInfo) {
  Smt2Driver driver{context_};
  EXPECT_TRUE(driver.ParseString("(get-info :status)"));
}

TEST_F(TestSmt2Driver, GetInfo) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(set-info :status sat)\n"
                         "(get-info :status)"));
}

TEST_F(TestSmt2Driver, Exit) {
  Smt2Driver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("(declare-fun x () Real)\n"
                         "(exit)\n"
                         "(declare-fun y () Real)"));
  const Variable& x = driver.LookupVariable("x");
  EXPECT_EQ(x.get_name(), "x");
  EXPECT_THROW(driver.LookupVariable("y"), std::out_of_range);
}
