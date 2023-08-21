/**
 * @file TestBox.cpp
 * @author dlinear
 * @date 16 Aug 2023
 * @copyright 2023 dlinear
 */
#include "dlinear/util/Box.h"
#include "tests/symbolic/TestSymbolicUtils.h"

#include <limits>
#include <type_traits>
#include <utility>
#include <vector>

#include <gtest/gtest.h>

#include "dlinear/util/infty.h"

using std::is_nothrow_move_constructible;
using std::numeric_limits;
using std::pair;
using std::vector;
using namespace dlinear;

class TestBox : public ::testing::Test {
 protected:
  DrakeSymbolicGuard guard_;
  // Real Variables.
  const Variable x_{"x"};
  const Variable y_{"y"};
  const Variable z_{"z"};
  const Variable w_{"w"};

#if 0
  // Integer Variables.
  const Variable i_{"i", Variable::Type::INTEGER};
  const Variable j_{"j", Variable::Type::INTEGER};

  // Binary Variables.
  const Variable b1_{"i", Variable::Type::BINARY};
  const Variable b2_{"j", Variable::Type::BINARY};
#endif

  const mpq_class inf_{mpq_infty()};
};

TEST_F(TestBox, AddHasVariable) {
  Box b1{{x_}};
  EXPECT_EQ(b1[x_].lb(), -inf_);
  EXPECT_EQ(b1[x_].ub(), inf_);

  EXPECT_TRUE(b1.has_variable(x_));
  EXPECT_FALSE(b1.has_variable(y_));
  EXPECT_FALSE(b1.has_variable(z_));

  b1.Add(y_);
  EXPECT_EQ(b1[y_].lb(), -inf_);
  EXPECT_EQ(b1[y_].ub(), inf_);
  EXPECT_TRUE(b1.has_variable(x_));
  EXPECT_TRUE(b1.has_variable(y_));
  EXPECT_FALSE(b1.has_variable(z_));

  b1.Add(z_, -5, 10);
  EXPECT_EQ(b1[z_].lb(), -5);
  EXPECT_EQ(b1[z_].ub(), 10);
  EXPECT_TRUE(b1.has_variable(x_));
  EXPECT_TRUE(b1.has_variable(y_));
  EXPECT_TRUE(b1.has_variable(z_));
}

TEST_F(TestBox, Empty) {
  Box b1{{x_}};
  EXPECT_FALSE(b1.empty());

  b1.set_empty();
  EXPECT_TRUE(b1.empty());
}

TEST_F(TestBox, IndexOperator) {
  Box b1;
  b1.Add(x_, 3, 5);
  b1.Add(y_, 6, 10);
  EXPECT_EQ(b1[0], b1[x_]);
  EXPECT_EQ(b1[1], b1[y_]);

  const Box b2{b1};
  EXPECT_EQ(b2[0], b2[x_]);
  EXPECT_EQ(b2[1], b2[y_]);
  EXPECT_EQ(b1[0], b2[x_]);
  EXPECT_EQ(b1[1], b2[y_]);
}

TEST_F(TestBox, IntervalVector) {
  Box b1;
  b1.Add(x_, 3, 5);
  b1.Add(y_, 6, 10);
  EXPECT_EQ(b1.interval_vector()[0], b1[x_]);

  // Update
  b1.mutable_interval_vector()[0] = Box::Interval(0, 1);
  EXPECT_EQ(b1[x_].lb(), 0);
  EXPECT_EQ(b1[x_].ub(), 1);

  const Box b2{b1};
  EXPECT_EQ(b2.interval_vector()[0].lb(), 0);
  EXPECT_EQ(b2.interval_vector()[0].ub(), 1);
}

TEST_F(TestBox, VariableVariables) {
  const Box b1{{x_, y_, z_}};
  vector<Variable> variables{x_, y_, z_};
  const vector<Variable> &variables_in_b1{b1.variables()};
  EXPECT_EQ(variables_in_b1.size(), 3ul);
  EXPECT_EQ(variables_in_b1[0], x_);
  EXPECT_EQ(variables_in_b1[1], y_);
  EXPECT_EQ(variables_in_b1[2], z_);
}

TEST_F(TestBox, Index) {
  const Box b1{{x_, y_, z_}};
  EXPECT_EQ(b1.index(x_), 0);
  EXPECT_EQ(b1.index(y_), 1);
  EXPECT_EQ(b1.index(z_), 2);
}

TEST_F(TestBox, MaxDiam) {
  Box b1;
  b1.Add(x_, -10, 10);
  b1.Add(y_, 5, 5);
  b1.Add(z_, -1, 1);

  const pair<mpq_class, int> maxdiam_result{b1.MaxDiam()};
  EXPECT_EQ(maxdiam_result.first, 20.0);
  EXPECT_EQ(b1.variable(maxdiam_result.second), x_);
}

TEST_F(TestBox, Sharing) {
  Box b1{{x_, y_}};
  // b1 is not shared yet, so we should just update its internal
  // states.
  b1.Add(z_);

  // Now, b1 and b2 are shared.
  Box b2{b1};

  // Internal structure of b2 should be cloned before updated. It makes sure
  // that b1 is not affected.
  b2.Add(w_);

  EXPECT_EQ(b1.size(), 3 /* x, y, z */);
  EXPECT_EQ(b2.size(), 4 /* x, y, z, w_ */);
}

#if 0
TEST_F(TestBox, InplaceUnion) {
  Box b1{{x_, y_}};
  b1[x_] = Box::Interval(0, 1);
  b1[y_] = Box::Interval(0, 1);

  Box b2{{x_, y_}};
  b2[x_] = Box::Interval(2, 3);
  b2[y_] = Box::Interval(3, 4);

  b1.InplaceUnion(b2);
  EXPECT_EQ(b1[x_], Box::Interval(0, 3));
  EXPECT_EQ(b1[y_], Box::Interval(0, 4));

  // No changes on b2.
  EXPECT_EQ(b2[x_], Box::Interval(2, 3));
  EXPECT_EQ(b2[y_], Box::Interval(3, 4));
}
#endif

TEST_F(TestBox, BisectReal) {
  Box box;
  box.Add(x_, -10, 10);
  box.Add(y_, -5, 5);

  const pair<Box, Box> p{box.bisect(x_)};
  const Box &box1{p.first};
  const Box &box2{p.second};

  EXPECT_EQ(box1[x_].lb(), box[x_].lb());
  EXPECT_EQ(box1[x_].ub(), 0);
  EXPECT_EQ(box1[y_], box[y_]);

  EXPECT_EQ(box2[x_].lb(), box1[x_].ub());
  EXPECT_EQ(box2[x_].ub(), box[x_].ub());
  EXPECT_EQ(box2[y_], box[y_]);
}

// QSopt_ex changes: Integer variables not supported (for now)
#if 0
TEST_F(TestBox, BisectInteger) {
  Box box;
  box.Add(x_, -10, 10);
  box.Add(i_, -5, 5);
  box.Add(b1_, 0, 1);

  const pair<Box, Box> p{box.bisect(i_)};
  const Box& box1{p.first};
  const Box& box2{p.second};

  EXPECT_EQ(box1[i_].lb(), box[i_].lb());
  EXPECT_EQ(box1[i_].ub(), 0.0);
  EXPECT_EQ(box1[x_], box[x_]);
  EXPECT_EQ(box1[b1_], box[b1_]);

  EXPECT_EQ(box2[i_].lb(), box1[i_].ub() + 1);
  EXPECT_EQ(box2[i_].ub(), box[i_].ub());
  EXPECT_EQ(box2[x_], box[x_]);
  EXPECT_EQ(box2[b1_], box[b1_]);
}

TEST_F(TestBox, BisectBinary) {
  Box box;
  box.Add(x_, -10, 10);
  box.Add(i_, -5, 5);
  box.Add(b1_, 0, 1);

  const pair<Box, Box> p{box.bisect(b1_)};
  const Box& box1{p.first};
  const Box& box2{p.second};

  EXPECT_EQ(box1[b1_].lb(), box[b1_].lb());
  EXPECT_EQ(box1[b1_].ub(), 0.0);
  EXPECT_EQ(box1[x_], box[x_]);
  EXPECT_EQ(box1[i_], box[i_]);

  EXPECT_EQ(box2[b1_].lb(), box1[b1_].ub() + 1);
  EXPECT_EQ(box2[b1_].ub(), box[b1_].ub());
  EXPECT_EQ(box2[x_], box[x_]);
  EXPECT_EQ(box2[i_], box[i_]);
}
#endif

// mpq_class changes: Non-zero intervals are _always_ bisectable!
#if 0
TEST_F(TestBox, NotBisectable) {
  Box box;
  // x = [10, 10 + ε]
  box.Add(x_, 10, std::nextafter(10, 11));

  // [10, 10 + ε] is not bisectable.
  EXPECT_THROW(box.bisect(x_), std::runtime_error);

  // y is not in the box -> non-bisectable.
  EXPECT_THROW(box.bisect(y_), std::runtime_error);
}
#endif

TEST_F(TestBox, Equality) {
  Box b1;
  b1.Add(x_, -10, 10);
  b1.Add(y_, -5, 5);

  Box b2{b1};
  EXPECT_TRUE(b1 == b2);
  EXPECT_FALSE(b1 != b2);

  b2.Add(z_, -1, 1);
  EXPECT_FALSE(b1 == b2);
  EXPECT_TRUE(b1 != b2);

  Box b3{b1};
  EXPECT_TRUE(b1 == b3);
  EXPECT_FALSE(b1 != b3);

  b3[y_] = Box::Interval(-5, 6);
  EXPECT_FALSE(b1 == b3);
  EXPECT_TRUE(b1 != b3);
}

// Checks types in Box are nothrow move-constructible so that the
// vectors including them can be processed efficiently.
TEST_F(TestBox, IsNothrowMoveConstructible) {
  static_assert(is_nothrow_move_constructible<Box::Interval>::value,
                "Box::Interval should be nothrow_move_constructible.");
  static_assert(is_nothrow_move_constructible<Box::IntervalVector>::value,
                "Box::IntervalVector should be nothrow_move_constructible.");
  static_assert(is_nothrow_move_constructible<Box>::value,
                "Box should be nothrow_move_constructible.");
}

TEST_F(TestBox, IntervalFromString) {
  Box::Interval interval = Box::Interval::fromString("100");
  EXPECT_EQ(interval.lb(), 100); // TODO: should be -100??
  EXPECT_EQ(interval.ub(), 100);
}
