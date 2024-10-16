/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gtest/gtest.h>

#include <limits>
#include <type_traits>
#include <utility>
#include <vector>

#ifdef DLINEAR_ENABLED_QSOPTEX
#include "dlinear/libs/libqsopt_ex.h"
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
#include "dlinear/libs/libsoplex.h"
#endif
#include "dlinear/util/Box.h"
#include "test/solver/TestSolverUtils.h"
#include "test/symbolic/TestSymbolicUtils.h"

using std::is_nothrow_move_constructible;
using std::numeric_limits;
using std::pair;
using std::vector;
using namespace dlinear;

class TestBox : public ::testing::TestWithParam<Config::LPSolver> {
 protected:
  // Real Variables.
  const Variable x_{"x"};
  const Variable y_{"y"};
  const Variable z_{"z"};
  const Variable w_{"w"};
  mpq_class inf_{
#ifdef DLINEAR_ENABLED_QSOPTEX
      GetParam() == Config::LPSolver::QSOPTEX ? mpq_class{mpq_INFTY} :
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
      GetParam() == Config::LPSolver::SOPLEX ? soplex::infinity
                                             :
#endif
                                             numeric_limits<double>::infinity()};
  Box box_{GetParam()};

#if 0
  // Integer Variables.
  const Variable i_{"i", Variable::Type::INTEGER};
  const Variable j_{"j", Variable::Type::INTEGER};

  // Binary Variables.
  const Variable box__{"i", Variable::Type::BINARY};
  const Variable b2_{"j", Variable::Type::BINARY};
#endif
};

INSTANTIATE_TEST_SUITE_P(TestSmt2, TestBox, enabled_test_solvers);

TEST_P(TestBox, AddHasVariable) {
  Box box{{x_}, GetParam()};
  DLINEAR_LOG_INIT_VERBOSITY(5);
  EXPECT_EQ(box[x_].lb(), -inf_);
  EXPECT_EQ(box[x_].ub(), inf_);

  EXPECT_TRUE(box.has_variable(x_));
  EXPECT_FALSE(box.has_variable(y_));
  EXPECT_FALSE(box.has_variable(z_));
  EXPECT_EQ(box.size(), 1);

  box.Add(y_);
  EXPECT_EQ(box[y_].lb(), -inf_);
  EXPECT_EQ(box[y_].ub(), inf_);
  EXPECT_TRUE(box.has_variable(x_));
  EXPECT_TRUE(box.has_variable(y_));
  EXPECT_FALSE(box.has_variable(z_));
  EXPECT_EQ(box.size(), 2);

  box.Add(z_, -5, 10);
  EXPECT_EQ(box[z_].lb(), -5);
  EXPECT_EQ(box[z_].ub(), 10);
  EXPECT_TRUE(box.has_variable(x_));
  EXPECT_TRUE(box.has_variable(y_));
  EXPECT_TRUE(box.has_variable(z_));
  EXPECT_EQ(box.size(), 3);
}

TEST_P(TestBox, Empty) {
  box_.Add(x_, 3, 5);
  EXPECT_FALSE(box_.empty());

  box_.set_empty();
  EXPECT_TRUE(box_.empty());

  EXPECT_TRUE(box_.has_variable(x_));
  EXPECT_EQ(box_.size(), 1);
  EXPECT_TRUE(box_[x_].is_empty());
}

TEST_P(TestBox, IndexOperator) {
  box_.Add(x_, 3, 5);
  box_.Add(y_, 6, 10);
  EXPECT_EQ(box_[0], box_[x_]);
  EXPECT_EQ(box_[1], box_[y_]);

  const Box b2{box_};
  EXPECT_EQ(b2[0], b2[x_]);
  EXPECT_EQ(b2[1], b2[y_]);
  EXPECT_EQ(box_[0], b2[x_]);
  EXPECT_EQ(box_[1], b2[y_]);
}

TEST_P(TestBox, IntervalVector) {
  box_.Add(x_, 3, 5);
  box_.Add(y_, 6, 10);
  EXPECT_EQ(box_.interval_vector()[0], box_[x_]);

  // Update
  box_.m_interval_vector()[0] = Interval(0, 1);
  EXPECT_EQ(box_[x_].lb(), 0);
  EXPECT_EQ(box_[x_].ub(), 1);

  const Box b2{box_};
  EXPECT_EQ(b2.interval_vector()[0].lb(), 0);
  EXPECT_EQ(b2.interval_vector()[0].ub(), 1);
}

TEST_P(TestBox, VariableVariables) {
  const Box box{{x_, y_, z_}, GetParam()};
  vector<Variable> variables{x_, y_, z_};
  const vector<Variable> &variables_in_box_{box.variables()};
  EXPECT_EQ(variables_in_box_.size(), 3ul);
  EXPECT_EQ(variables_in_box_[0], x_);
  EXPECT_EQ(variables_in_box_[1], y_);
  EXPECT_EQ(variables_in_box_[2], z_);
}

TEST_P(TestBox, Index) {
  const Box box{{x_, y_, z_}, GetParam()};
  EXPECT_EQ(box.index(x_), 0);
  EXPECT_EQ(box.index(y_), 1);
  EXPECT_EQ(box.index(z_), 2);
}

TEST_P(TestBox, MaxDiam) {
  box_.Add(x_, -10, 10);
  box_.Add(y_, 5, 5);
  box_.Add(z_, -1, 1);

  const pair<mpq_class, int> maxdiam_result{box_.MaxDiam()};
  EXPECT_EQ(maxdiam_result.first, 20.0);
  EXPECT_EQ(box_.variable(maxdiam_result.second), x_);
}

TEST_P(TestBox, Sharing) {
  Box box{{x_, y_}, GetParam()};
  // box_ is not shared yet, so we should just update its internal
  // states.
  box.Add(z_);

  // Now, box_ and b2 are shared.
  Box box2{box};

  // Internal structure of b2 should be cloned before updated. It makes sure
  // that box_ is not affected.
  box2.Add(w_);

  EXPECT_EQ(box.size(), 3 /* x, y, z */);
  EXPECT_EQ(box2.size(), 4 /* x, y, z, w_ */);
}

#if 0
TEST_P(TestBox, InplaceUnion) {
  Box box_{{x_, y_}};
  box_[x_] = Interval(0, 1);
  box_[y_] = Interval(0, 1);

  Box b2{{x_, y_}};
  b2[x_] = Interval(2, 3);
  b2[y_] = Interval(3, 4);

  box_.InplaceUnion(b2);
  EXPECT_EQ(box_[x_], Interval(0, 3));
  EXPECT_EQ(box_[y_], Interval(0, 4));

  // No changes on b2.
  EXPECT_EQ(b2[x_], Interval(2, 3));
  EXPECT_EQ(b2[y_], Interval(3, 4));
}
#endif

TEST_P(TestBox, BisectReal) {
  box_.Add(x_, -10, 10);
  box_.Add(y_, -5, 5);

  const pair<Box, Box> p{box_.Bisect(x_)};
  const Box &box1{p.first};
  const Box &box2{p.second};

  EXPECT_EQ(box1[x_].lb(), box_[x_].lb());
  EXPECT_EQ(box1[x_].ub(), 0);
  EXPECT_EQ(box1[y_], box_[y_]);

  EXPECT_EQ(box2[x_].lb(), box1[x_].ub());
  EXPECT_EQ(box2[x_].ub(), box_[x_].ub());
  EXPECT_EQ(box2[y_], box_[y_]);
}

// QSopt_ex changes: Integer variables not supported (for now)
#if 0
TEST_P(TestBox, BisectInteger) {
  Box box;
  box.Add(x_, -10, 10);
  box.Add(i_, -5, 5);
  box.Add(box__, 0, 1);

  const pair<Box, Box> p{box.bisect(i_)};
  const Box& box1{p.first};
  const Box& box2{p.second};

  EXPECT_EQ(box1[i_].lb(), box[i_].lb());
  EXPECT_EQ(box1[i_].ub(), 0.0);
  EXPECT_EQ(box1[x_], box[x_]);
  EXPECT_EQ(box1[box__], box[box__]);

  EXPECT_EQ(box2[i_].lb(), box1[i_].ub() + 1);
  EXPECT_EQ(box2[i_].ub(), box[i_].ub());
  EXPECT_EQ(box2[x_], box[x_]);
  EXPECT_EQ(box2[box__], box[box__]);
}

TEST_P(TestBox, BisectBinary) {
  Box box;
  box.Add(x_, -10, 10);
  box.Add(i_, -5, 5);
  box.Add(box__, 0, 1);

  const pair<Box, Box> p{box.bisect(box__)};
  const Box& box1{p.first};
  const Box& box2{p.second};

  EXPECT_EQ(box1[box__].lb(), box[box__].lb());
  EXPECT_EQ(box1[box__].ub(), 0.0);
  EXPECT_EQ(box1[x_], box[x_]);
  EXPECT_EQ(box1[i_], box[i_]);

  EXPECT_EQ(box2[box__].lb(), box1[box__].ub() + 1);
  EXPECT_EQ(box2[box__].ub(), box[box__].ub());
  EXPECT_EQ(box2[x_], box[x_]);
  EXPECT_EQ(box2[i_], box[i_]);
}
#endif

// mpq_class changes: Non-zero intervals are _always_ bisectable!
#if 0
TEST_P(TestBox, NotBisectable) {
  Box box;
  // x = [10, 10 + ε]
  box.Add(x_, 10, std::nextafter(10, 11));

  // [10, 10 + ε] is not bisectable.
  EXPECT_THROW(box.bisect(x_), std::runtime_error);

  // y is not in the box -> non-bisectable.
  EXPECT_THROW(box.bisect(y_), std::runtime_error);
}
#endif

TEST_P(TestBox, Equality) {
  box_.Add(x_, -10, 10);
  box_.Add(y_, -5, 5);

  Box b2{box_};
  EXPECT_TRUE(box_ == b2);
  EXPECT_FALSE(box_ != b2);

  b2.Add(z_, -1, 1);
  EXPECT_FALSE(box_ == b2);
  EXPECT_TRUE(box_ != b2);

  Box b3{box_};
  EXPECT_TRUE(box_ == b3);
  EXPECT_FALSE(box_ != b3);

  b3[y_] = Interval(-5, 6);
  EXPECT_FALSE(box_ == b3);
  EXPECT_TRUE(box_ != b3);
}

// Checks types in Box are nothrow move-constructible so that the vectors including them can be processed efficiently.
TEST_P(TestBox, IsNothrowMoveConstructible) {
  static_assert(is_nothrow_move_constructible<Interval>::value, "Interval should be nothrow_move_constructible.");
  static_assert(is_nothrow_move_constructible<std::vector<Interval>>::value,
                "IntervalVector should be nothrow_move_constructible.");
}

TEST_P(TestBox, IntervalFromString) {
  Interval interval = Interval::FromString("100");
  EXPECT_EQ(interval.lb(), 100);  // TODO: should be -100??
  EXPECT_EQ(interval.ub(), 100);
}
