/**
 * @file TestMpsDriver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include "dlinear/parser/mps/Driver.h"
#include "test/symbolic/TestSymbolicUtils.h"

using dlinear::Config;
using dlinear::Context;
using dlinear::Variable;
using dlinear::mps::MpsDriver;

class TestMpsDriver : public ::testing::Test {
  const DrakeSymbolicGuard guard_;

 protected:
  Config config_;
  Context context_{config_};
};

TEST_F(TestMpsDriver, SetConfigOptions1) {
  MpsDriver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("* @set-option :precision 1\n"
                         "* @set-option :produce-models true\n"
                         "* @set-option :polytope true\n"
                         "* @set-option :forall-polytope true\n"
                         "* @set-option :local-optimization true\n"
                         "* @set-option :worklist-fixpoint true\n"
                         "ENDATA"));
  EXPECT_EQ(driver.context().config().precision(), 1);
  EXPECT_TRUE(driver.context().config().produce_models());
  EXPECT_TRUE(driver.context().config().use_polytope());
  EXPECT_TRUE(driver.context().config().use_polytope_in_forall());
  EXPECT_TRUE(driver.context().config().use_local_optimization());
  EXPECT_TRUE(driver.context().config().use_worklist_fixpoint());
}

TEST_F(TestMpsDriver, SetConfigOptions2) {
  MpsDriver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("* @set-option :precision 0.505\n"
                         "* @set-option :produce-models false\n"
                         "* @set-option :polytope false\n"
                         "* @set-option :forall-polytope false\n"
                         "* @set-option :local-optimization false\n"
                         "* @set-option :worklist-fixpoint false\n"
                         "ENDATA"));
  EXPECT_EQ(driver.context().config().precision(), 0.505);
  EXPECT_FALSE(driver.context().config().produce_models());
  EXPECT_FALSE(driver.context().config().use_polytope());
  EXPECT_FALSE(driver.context().config().use_polytope_in_forall());
  EXPECT_FALSE(driver.context().config().use_local_optimization());
  EXPECT_FALSE(driver.context().config().use_worklist_fixpoint());
}
