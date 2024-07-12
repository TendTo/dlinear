/**
 * @file TestIfThenElseEliminator.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include <vector>

#include "TestSymbolicUtils.h"
#include "dlinear/symbolic/IfThenElseEliminator.h"

using dlinear::IfThenElseEliminator;
using std::int64_t;
using std::numeric_limits;
using std::runtime_error;
using std::vector;

class TestIfThenElseEliminator : public ::testing::Test {
 protected:
  const Variable x_{"x", Variable::Type::CONTINUOUS};
  const Variable y_{"y", Variable::Type::CONTINUOUS};
  const Variable z_{"z", Variable::Type::CONTINUOUS};
  const Variable w_{"w", Variable::Type::CONTINUOUS};

  const Variable b1_{"b1", Variable::Type::BOOLEAN};
  const Variable b2_{"b2", Variable::Type::BOOLEAN};
  const Variable b3_{"b3", Variable::Type::BOOLEAN};

  // The following formulas do not include if-then-else expressions
  // and as a result should not be changed in the process of ite-elim.
  const vector<Formula> non_ites_{
      // clang-format off
      Formula::True(),
      Formula::False(),
      // Relational operators
      x_ + y_ == z_,
      x_ + y_ != z_,
      x_ + y_ > z_,
      x_ + y_ >= z_,
      x_ + y_ < z_,
      x_ + y_ <= z_,
      // Constant
      y_ == 4,
      // Addition, multiplication, division
      1 + x_ + y_ * 3 / z_ == 0,
      // math functions
      log(x_) == abs(y_),
      exp(x_) > sqrt(y_),
      pow(x_, y_) < sin(z_),
      cos(x_) >= tan(y_),
      asin(x_) <= acos(y_),
      atan(x_) >= atan2(y_, z_),
      sinh(x_) == cosh(y_),
      tanh(x_) == min(y_, z_),
      max(x_, y_) != z_,
      !b1_,
      dlinear::drake::symbolic::uninterpreted_function("uf", {x_, y_, z_}) == 0.0,
      (b1_ && b2_) || (!b1_ && !b2_),
      // clang-format on
  };
};

TEST_F(TestIfThenElseEliminator, NonITEs) {
  for (const Formula &f : non_ites_) {
    IfThenElseEliminator ite_elim{{}};
    EXPECT_PRED2(FormulaEqual, f, ite_elim.Process(f));
  }
}

TEST_F(TestIfThenElseEliminator, NonITEsInForall) {
  for (const Formula &f : non_ites_) {
    IfThenElseEliminator ite_elim{{}};
    const Formula forall_f{forall({x_}, f)};
    EXPECT_PRED2(FormulaEqual, forall_f, ite_elim.Process(forall_f));
  }
}

TEST_F(TestIfThenElseEliminator, ITEs) {
  const Formula f{if_then_else(x_ > y_, x_ + 1.0, y_ + 1.0) == z_};
  IfThenElseEliminator ite_elim{{}};
  const Formula converted = ite_elim.Process(f);
  ASSERT_FALSE(ite_elim.variables().empty());
  ASSERT_EQ(ite_elim.variables().size(), 1u);
  const Variable &ite_var{ite_elim.variables().begin()->second};
  const Formula expected{ite_var == z_ && (!(x_ > y_) || ite_var == x_ + 1.0) && (x_ > y_ || ite_var == y_ + 1.0)};
  EXPECT_PRED2(FormulaNotEqual, f, converted);
  EXPECT_PRED2(FormulaEqual, converted, expected);
}

TEST_F(TestIfThenElseEliminator, NestedITEs) {
  const Expression e1{if_then_else(Formula{b1_}, x_, y_)};
  const Expression e2{if_then_else(Formula{b2_}, z_, w_)};
  const Expression e{if_then_else(Formula{b3_}, e1, e2)};
  const Formula f{e > 0};
  IfThenElseEliminator ite_elim{{}};
  const Formula processed{ite_elim.Process(f)};
  EXPECT_EQ(processed.to_string(),
            "((ITE0 > 0) and (b3 or (ITE0 == ITE2)) and ((ITE0 == ITE1) or "
            "!(b3)) and ((ITE1 == x) or !((b1 and b3))) and ((ITE1 == y) or "
            "!((b3 and !(b1)))) and ((ITE2 == z) or !((b2 and !(b3)))) and "
            "((ITE2 == w) or !((!(b2) and !(b3)))))");
}

TEST_F(TestIfThenElseEliminator, ITEsInForall) {
  const Formula f{forall({y_}, if_then_else(x_ > y_, x_, y_) > 0)};
  IfThenElseEliminator ite_elim{{}};
  const Formula processed{ite_elim.Process(f)};
  EXPECT_EQ(processed.to_string(),
            "forall({y, ITE0}. ((ITE0 > 0) or ((x > y) and !((ITE0 == x))) or (!((ITE0 == y)) and !((x > y)))))");
}

// TODO: Add theory propagation to ITE eliminator
//TEST_F(TestIfThenElseEliminator, ITEPropagateFalse) {
//  const Expression e1{if_then_else(Formula{b1_}, 1, 2)};
//  const Expression e2{if_then_else(Formula{b2_}, 3, 4)};
//  const Formula f{e1 == e2};
//  IfThenElseEliminator ite_elim{{}};
//  const Formula processed{ite_elim.Process(f)};
//  EXPECT_EQ(processed.to_string(), "False");
//}

TEST_F(TestIfThenElseEliminator, ITETrue) {
  const Expression e1{if_then_else(Formula::True(), x_, y_)};
  const Formula f{e1 == y_};
  IfThenElseEliminator ite_elim{{}};
  const Formula processed{ite_elim.Process(f)};
  EXPECT_EQ(processed.to_string(), "(x == y)");
}

TEST_F(TestIfThenElseEliminator, ITEFalse) {
  const Expression e1{if_then_else(Formula::False(), x_, y_)};
  const Formula f{e1 == y_};
  IfThenElseEliminator ite_elim{{}};
  const Formula processed{ite_elim.Process(f)};
  EXPECT_EQ(processed.to_string(), "True");
}

TEST_F(TestIfThenElseEliminator, ITESame) {
  const Expression e1{if_then_else(Formula{b1_}, x_, x_)};
  const Formula f{e1 == y_};
  IfThenElseEliminator ite_elim{{}};
  const Formula processed{ite_elim.Process(f)};
  EXPECT_EQ(processed.to_string(), "(x == y)");
}

TEST_F(TestIfThenElseEliminator, ITESameTrue) {
  const Expression e1{if_then_else(Formula{b1_}, y_, y_)};
  const Formula f{e1 == y_};
  IfThenElseEliminator ite_elim{{}};
  const Formula processed{ite_elim.Process(f)};
  EXPECT_EQ(processed.to_string(), "True");
}

TEST_F(TestIfThenElseEliminator, ITESimplifyNestedTrue) {
  const Expression e1{if_then_else(Formula{b1_}, x_, y_)};
  const Expression e2{if_then_else(Formula{b1_}, e1, z_)};
  const Formula f{e2 == 0};
  IfThenElseEliminator ite_elim{{}};
  const Formula processed{ite_elim.Process(f)};
  EXPECT_EQ(processed.to_string(), "((ITE0 == 0) and (b1 or (ITE0 == z)) and ((ITE0 == x) or !(b1)))");
}

TEST_F(TestIfThenElseEliminator, ITESimplifyNestedFalse) {
  const Expression e1{if_then_else(Formula{b1_}, x_, y_)};
  const Expression e2{if_then_else(!Formula{b1_}, e1, z_)};
  const Formula f{e2 == 0};
  IfThenElseEliminator ite_elim{{}};
  const Formula processed{ite_elim.Process(f)};
  EXPECT_EQ(processed.to_string(), "((ITE0 == 0) and (b1 or (ITE0 == y)) and ((ITE0 == z) or !(b1)))");
}

// TODO: Add theory propagation to ITE eliminator
//TEST_F(TestIfThenElseEliminator, ITESimplifyNestedConstantsFalse) {
//  const Expression e1{if_then_else(Formula{b2_}, 1, 2)};
//  const Expression e2{if_then_else(!Formula{b2_}, e1, 3)};
//  const Formula f{e2 == 4};
//  IfThenElseEliminator ite_elim{{}};
//  const Formula processed{ite_elim.Process(f)};
//  EXPECT_EQ(processed.to_string(), "False");
//}
