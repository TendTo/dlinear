/**
 * @file TestIfThenElseEliminator.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "dlinear/symbolic/IfThenElseEliminator.h"
#include "TestSymbolicUtils.h"
#include <vector>
#include <gtest/gtest.h>

using std::int64_t;
using std::numeric_limits;
using std::runtime_error;
using std::vector;
using dlinear::IfThenElseEliminator;

class TestIfThenElseEliminator : public ::testing::Test {
  DrakeSymbolicGuard guard_;
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
    IfThenElseEliminator ite_elim;
    EXPECT_PRED2(FormulaEqual, f, ite_elim.Process(f));
  }
}

TEST_F(TestIfThenElseEliminator, NonITEsInForall) {
  for (const Formula &f : non_ites_) {
    IfThenElseEliminator ite_elim;
    const Formula forall_f{forall({x_}, f)};
    EXPECT_PRED2(FormulaEqual, forall_f, ite_elim.Process(forall_f));
  }
}

TEST_F(TestIfThenElseEliminator, ITEs) {
  const Formula f{if_then_else(x_ > y_, x_ + 1.0, y_ + 1.0) == z_};
  IfThenElseEliminator ite_elim;
  const Formula converted = ite_elim.Process(f);
  ASSERT_FALSE(ite_elim.variables().empty());
  ASSERT_EQ(ite_elim.variables().size(), 1);
  const Variable &ite_var{*(ite_elim.variables().begin())};
  const Formula expected{ite_var == z_ &&
      (!(x_ > y_) || ite_var == x_ + 1.0) &&
      (x_ > y_ || ite_var == y_ + 1.0)};
  EXPECT_PRED2(FormulaNotEqual, f, converted);
  EXPECT_PRED2(FormulaEqual, converted, expected);
}

TEST_F(TestIfThenElseEliminator, NestedITEs) {
  const Expression e1{if_then_else(Formula{b1_}, x_, y_)};
  const Expression e2{if_then_else(Formula{b2_}, z_, w_)};
  const Expression e{if_then_else(Formula{b3_}, e1, e2)};
  const Formula f{e > 0};
  IfThenElseEliminator ite_elim;
  const Formula processed{ite_elim.Process(f)};
  EXPECT_EQ(processed.to_string(),
            "((ITE1 > 0) and (b3 or (ITE1 == ITE3)) and ((ITE1 == ITE2) or "
            "!(b3)) and ((ITE2 == x) or !((b1 and b3))) and ((ITE2 == y) or "
            "!((b3 and !(b1)))) and ((ITE3 == z) or !((b2 and !(b3)))) and "
            "((ITE3 == w) or !((!(b2) and !(b3)))))");
}

TEST_F(TestIfThenElseEliminator, ITEsInForall) {
  const Formula f{forall({y_}, if_then_else(x_ > y_, x_, y_) > 0)};
  IfThenElseEliminator ite_elim;
  const Formula processed{ite_elim.Process(f)};
  EXPECT_EQ(processed.to_string(),
            "forall({y, ITE4}. ((ITE4 > 0) or ((x > y) and !((ITE4 == x))) or "
            "(!((ITE4 == y)) and !((x > y)))))");
}
