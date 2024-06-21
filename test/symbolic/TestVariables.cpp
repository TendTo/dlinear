/**
 * @file TestVariables.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include "dlinear/symbolic/Variables.h"

using dlinear::DefaultHashAlgorithm;
using dlinear::symbolic::Variable;
using dlinear::symbolic::Variables;

class TestVariables : public ::testing::Test {
 protected:
  const Variable x_{"x"};
  const Variable y_{"y"};
  const Variable w_{"w"};
  const Variable z_{"z"};
  Variables vars_;

  TestVariables() {
    vars_.insert(x_);
    vars_.insert(y_);
    vars_.insert(z_);
  }
};

TEST_F(TestVariables, Size) { EXPECT_EQ(vars_.size(), 3u); }

TEST_F(TestVariables, Empty) { EXPECT_FALSE(vars_.empty()); }

TEST_F(TestVariables, Insert) {
  vars_.insert(w_);
  EXPECT_EQ(vars_.size(), 4u);
  EXPECT_TRUE(vars_.include(w_));
}

TEST_F(TestVariables, Erase) {
  vars_.erase(y_);
  EXPECT_EQ(vars_.size(), 2u);
  EXPECT_FALSE(vars_.include(y_));
}

TEST_F(TestVariables, Find) {
  auto it = vars_.find(x_);
  EXPECT_NE(it, vars_.end());
  EXPECT_TRUE(std::equal_to<Variable>{}(*it, x_));
}

TEST_F(TestVariables, OperatorPlus) {
  Variables other;
  other.insert(w_);
  Variables result = vars_ + other;
  EXPECT_EQ(result.size(), 4u);
  EXPECT_TRUE(result.include(w_));
}

TEST_F(TestVariables, OperatorMinus) {
  Variables other;
  other.insert(y_);
  Variables result = vars_ - other;
  EXPECT_EQ(result.size(), 2u);
  EXPECT_FALSE(result.include(y_));
}

TEST_F(TestVariables, Intersect) {
  Variables other;
  other.insert(y_);
  other.insert(w_);
  Variables result = vars_.intersect(other);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_TRUE(result.include(y_));
}

TEST_F(TestVariables, EqualityOperator) {
  Variables other;
  other.insert(x_);
  other.insert(y_);
  other.insert(z_);
  EXPECT_TRUE(vars_ == other);
}

TEST_F(TestVariables, LessThanOperator) {
  Variables other;
  other.insert(y_);
  other.insert(x_);
  EXPECT_TRUE(other < vars_);
}

TEST_F(TestVariables, SubsetChecking) {
  Variables subset;
  subset.insert(z_);
  subset.insert(y_);
  EXPECT_TRUE(subset.IsSubsetOf(vars_));
  EXPECT_FALSE(vars_.IsSubsetOf(subset));
  EXPECT_TRUE(vars_.IsSupersetOf(subset));
  EXPECT_FALSE(subset.IsSupersetOf(vars_));
  EXPECT_TRUE(subset.IsStrictSubsetOf(vars_));
  EXPECT_FALSE(vars_.IsStrictSubsetOf(subset));
  EXPECT_TRUE(vars_.IsStrictSupersetOf(subset));
  EXPECT_FALSE(subset.IsStrictSupersetOf(vars_));
}

TEST_F(TestVariables, Ostream) { EXPECT_NO_THROW(std::cout << vars_ << std::endl); }
