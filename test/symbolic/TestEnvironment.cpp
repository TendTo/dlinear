/**
 * @file TestVariable.cpp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 */

#include <gtest/gtest.h>

#include "dlinear/symbolic/Environment.h"

using dlinear::symbolic::Environment;
using dlinear::symbolic::Variable;
using dlinear::symbolic::Variables;

class TestEnvironment : public ::testing::Test {
 protected:
  const Variable var_{"var"};
  const Variable var2_{"var2"};
  const Variable var3_{"var3"};
};

TEST_F(TestEnvironment, EmpyEnvironment) {
  const Environment env{};
  EXPECT_TRUE(env.empty());
  EXPECT_EQ(env.size(), 0);
  EXPECT_TRUE(env.to_string().empty());
}

TEST_F(TestEnvironment, DefaultToZeroEnvironment) {
  const Environment env{var_};
  EXPECT_FALSE(env.empty());
  EXPECT_EQ(env.size(), 1);
  EXPECT_EQ(env[var_], 0);
}

TEST_F(TestEnvironment, InitListZeroEnvironment) {
  const Environment env{var_, var2_, var3_};
  EXPECT_FALSE(env.empty());
  EXPECT_EQ(env.size(), 3);
  EXPECT_EQ(env[var_], 0);
  EXPECT_EQ(env[var2_], 0);
  EXPECT_EQ(env[var3_], 0);
}

TEST_F(TestEnvironment, InitListEnvironment) {
  const Environment env{{var_, 1}, {var2_, 2}, {var3_, 3}};
  EXPECT_FALSE(env.empty());
  EXPECT_EQ(env.size(), 3);
  EXPECT_EQ(env[var_], 1);
  EXPECT_EQ(env[var2_], 2);
  EXPECT_EQ(env[var3_], 3);
}

TEST_F(TestEnvironment, UpdateEnvironmentValue) {
  Environment env{{var_, 1}, {var2_, 2}, {var3_, 3}};
  env[var_] = 4;
  EXPECT_FALSE(env.empty());
  EXPECT_EQ(env.size(), 3);
  EXPECT_EQ(env[var_], 4);
  EXPECT_EQ(env[var2_], 2);
  EXPECT_EQ(env[var3_], 3);
}

TEST_F(TestEnvironment, Domain) {
  Environment env{{var_, 1}, {var2_, 2}, {var3_, 3}};
  Variables domain{env.domain()};
  EXPECT_EQ(domain.size(), env.size());
  EXPECT_TRUE(domain.include(var_));
  EXPECT_TRUE(domain.include(var2_));
  EXPECT_TRUE(domain.include(var3_));
}
