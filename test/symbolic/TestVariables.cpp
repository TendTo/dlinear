/**
 * @file TestVariable.cpp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 */

#include <gtest/gtest.h>

#include "dlinear/symbolic/Variables.h"

using dlinear::symbolic::Variable;
using dlinear::symbolic::Variables;

class TestVariables : public ::testing::Test {
 protected:
  const Variable var_{"var"};
  const Variable var2_{"var2"};
  const Variable var3_{"var3"};
};

TEST_F(TestVariables, EmptyVariables) {
  const Variables vars{};
  EXPECT_TRUE(vars.empty());
  EXPECT_EQ(vars.size(), 0);
  EXPECT_EQ(vars.to_string(), "{}");
  EXPECT_EQ(vars.begin(), vars.end());
  EXPECT_EQ(vars.rbegin(), vars.rend());
}

TEST_F(TestVariables, OneVariables) {
  const Variables vars{var_};
  EXPECT_FALSE(vars.empty());
  EXPECT_EQ(vars.size(), 1);
  EXPECT_EQ(vars.to_string(), "{var}");
}

TEST_F(TestVariables, InsertVariables) {
  Variables vars{var_};
  vars.insert(var2_);
  EXPECT_FALSE(vars.empty());
  EXPECT_EQ(vars.size(), 2);
}

TEST_F(TestVariables, InsertSameVariables) {
  Variables vars{var_};
  vars.insert(var_);
  EXPECT_FALSE(vars.empty());
  EXPECT_EQ(vars.size(), 1);
}

TEST_F(TestVariables, InsertOtherVariables) {
  Variables vars{var_, var3_};
  Variables other_vars{var_, var2_};
  vars.insert(other_vars);
  EXPECT_FALSE(vars.empty());
  EXPECT_EQ(vars.size(), 3);
}

TEST_F(TestVariables, EraseVariables) {
  Variables vars{var_, var2_};
  size_t n_erase = vars.erase(var_);
  EXPECT_FALSE(vars.empty());
  EXPECT_EQ(vars.size(), 1);
  EXPECT_EQ(n_erase, 1);
}

TEST_F(TestVariables, EraseMissingVariables) {
  Variables vars{var_};
  size_t n_erase = vars.erase(var2_);
  EXPECT_FALSE(vars.empty());
  EXPECT_EQ(vars.size(), 1);
  EXPECT_EQ(n_erase, 0);
}

TEST_F(TestVariables, EraseOtherVariables) {
  Variables vars{var_, var2_};
  Variables other_vars{var_, var3_};
  size_t n_erase = vars.erase(other_vars);
  EXPECT_FALSE(vars.empty());
  EXPECT_EQ(vars.size(), 1);
  EXPECT_EQ(n_erase, 1);
}

TEST_F(TestVariables, IsSubsetOf) {
  Variables vars{var_};
  Variables other_vars{var_, var2_};
  EXPECT_TRUE(vars.IsSubsetOf(other_vars));
}

TEST_F(TestVariables, IsSubsetOfEq) {
  Variables vars{var_};
  EXPECT_TRUE(vars.IsSubsetOf(vars));
}

TEST_F(TestVariables, IsSubsetOfFail) {
  Variables vars{var_};
  Variables other_vars{var_, var2_};
  EXPECT_FALSE(other_vars.IsSubsetOf(vars));
}

TEST_F(TestVariables, IsStrictSubsetOf) {
  Variables vars{var_};
  Variables other_vars{var_, var2_};
  EXPECT_TRUE(vars.IsStrictSubsetOf(other_vars));
}

TEST_F(TestVariables, IsStrictSubsetOfFailEq) {
  Variables vars{var_};
  EXPECT_FALSE(vars.IsStrictSubsetOf(vars));
}

TEST_F(TestVariables, IsStrictSubsetOfFail) {
  Variables vars{var_};
  Variables other_vars{var_, var2_};
  EXPECT_FALSE(other_vars.IsStrictSubsetOf(vars));
}

TEST_F(TestVariables, IsSupersetOf) {
  Variables vars{var_, var2_};
  Variables other_vars{var_};
  EXPECT_TRUE(vars.IsSupersetOf(other_vars));
}

TEST_F(TestVariables, IsSupersetOfEq) {
  Variables vars{var_};
  EXPECT_TRUE(vars.IsSupersetOf(vars));
}

TEST_F(TestVariables, IsSupersetOfFail) {
  Variables vars{var_, var2_};
  Variables other_vars{var_};
  EXPECT_FALSE(other_vars.IsSupersetOf(vars));
}

TEST_F(TestVariables, IsStrictSupersetOf) {
  Variables vars{var_, var2_};
  Variables other_vars{var_};
  EXPECT_TRUE(vars.IsStrictSupersetOf(other_vars));
}

TEST_F(TestVariables, IsStrictSupersetOfFailEq) {
  Variables vars{var_};
  EXPECT_FALSE(vars.IsStrictSupersetOf(vars));
}

TEST_F(TestVariables, IsStrictSupersetOfFail) {
  Variables vars{var_, var2_};
  Variables other_vars{var_};
  EXPECT_FALSE(other_vars.IsStrictSupersetOf(vars));
}

TEST_F(TestVariables, Include) {
  Variables vars{var_};
  EXPECT_TRUE(vars.include(var_));
  EXPECT_FALSE(vars.include(var2_));
}

TEST_F(TestVariables, Find) {
  Variables vars{var_};
  EXPECT_NE(vars.find(var_), vars.end());
  EXPECT_EQ(vars.find(var2_), vars.end());
}
