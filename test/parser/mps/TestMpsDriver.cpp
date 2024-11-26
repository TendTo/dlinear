/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "dlinear/parser/mps/Driver.h"
#include "test/symbolic/TestSymbolicUtils.h"

using dlinear::Config;
using dlinear::Context;
using dlinear::Variable;
using dlinear::mps::MpsDriver;

class TestMpsDriver : public ::testing::Test {
 protected:
  Config config_{Config::Format::MPS};
  Context context_{config_};
};

TEST_F(TestMpsDriver, SetConfigOptions1) {
  MpsDriver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("* @set-option :precision 1\n"
                         "* @set-option :produce-models true\n"
                         "ENDATA"));
  EXPECT_EQ(driver.context().config().precision(), 1);
  EXPECT_TRUE(driver.context().config().produce_models());
}

TEST_F(TestMpsDriver, SetConfigOptions2) {
  MpsDriver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("* @set-option :precision 0.505\n"
                         "* @set-option :produce-models false\n"
                         "ENDATA"));
  EXPECT_EQ(driver.context().config().precision(), 0.505);
  EXPECT_FALSE(driver.context().config().produce_models());
}

TEST_F(TestMpsDriver, Name) {
  MpsDriver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("NAME best name ever\n"
                         "ENDATA"));
  EXPECT_EQ(driver.problem_name(), "best name ever");
}

TEST_F(TestMpsDriver, Rows) {
  MpsDriver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("ROWS\n"
                         " L  R1\n"
                         " G  R2\n"
                         " E  R3\n"
                         " E  R4\n"  // ignored row
                         " N  Ob\n"  // only used for  objective
                         "COLUMNS\n"
                         " X1 R1 1.\n"
                         " X1 R2 2.\n"
                         " X1 R3 3.\n"
                         " X1 Ob 4.\n"
                         "BOUNDS\n"
                         " FR BND X1\n"
                         "ENDATA"));
  EXPECT_EQ(driver.context().box().size(), 1);
  const Variable& x = driver.context().box().variable(0);
  EXPECT_EQ(driver.context().assertions().size(), 3u);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(x <= 0));
  EXPECT_TRUE(driver.context().assertions()[1].EqualTo(2 * x >= 0));
  EXPECT_TRUE(driver.context().assertions()[2].EqualTo(3 * x == 0));
}

TEST_F(TestMpsDriver, Columns) {
  MpsDriver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("ROWS\n"
                         " L  R1\n"
                         " G  R2\n"
                         " E  R3\n"
                         " N  Ob\n"
                         "COLUMNS\n"
                         " X1 R1 11 R2 12.0 \n"
                         " X2 R2 21.00 \n"
                         " X3 R1 31/1 R2 32 \n"
                         " X3 R3 33  \n"
                         "BOUNDS\n"
                         " FR BND X1\n"
                         " FR BND X2\n"
                         " FR BND X3\n"
                         "ENDATA"));
  EXPECT_EQ(driver.context().box().size(), 3);
  const Variable& x1 = driver.context().box().variable(0);
  const Variable& x2 = driver.context().box().variable(1);
  const Variable& x3 = driver.context().box().variable(2);
  EXPECT_EQ(driver.context().assertions().size(), 3u);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(11 * x1 + 31 * x3 <= 0));
  EXPECT_TRUE(driver.context().assertions()[1].EqualTo(12 * x1 + 21 * x2 + 32 * x3 >= 0));
  EXPECT_TRUE(driver.context().assertions()[2].EqualTo(33 * x3 == 0));
}

TEST_F(TestMpsDriver, Rhs) {
  MpsDriver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("ROWS\n"
                         " L  R1\n"
                         " G  R2\n"
                         " E  R3\n"
                         " N  Ob\n"
                         "COLUMNS\n"
                         " X1 R1 11 R2 12.0 \n"
                         " X2 R2 21.00 \n"
                         " X3 R1 31/1 R2 32 \n"
                         " X3 R3 33  \n"
                         "RHS\n"
                         " R1 1\n"
                         " R2 2 R3 3\n"
                         "BOUNDS\n"
                         " FR BND X1\n"
                         " FR BND X2\n"
                         " FR BND X3\n"
                         "ENDATA"));
  EXPECT_EQ(driver.context().box().size(), 3);
  const Variable& x1 = driver.context().box().variable(0);
  const Variable& x2 = driver.context().box().variable(1);
  const Variable& x3 = driver.context().box().variable(2);
  EXPECT_EQ(driver.context().assertions().size(), 3u);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(11 * x1 + 31 * x3 <= 1));
  EXPECT_TRUE(driver.context().assertions()[1].EqualTo(12 * x1 + 21 * x2 + 32 * x3 >= 2));
  EXPECT_TRUE(driver.context().assertions()[2].EqualTo(33 * x3 == 3));
}

TEST_F(TestMpsDriver, RangePositive) {
  MpsDriver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("ROWS\n"
                         " L  R1\n"
                         " G  R2\n"
                         " E  R3\n"
                         " N  Ob\n"
                         "COLUMNS\n"
                         " X1 R1 11 R2 12.0 \n"
                         " X2 R2 21.00 \n"
                         " X3 R1 31/1 R2 32 \n"
                         " X3 R3 33 \n"
                         "RHS\n"
                         " R1 1\n"
                         " R2 2 R3 3\n"
                         "RANGES\n"
                         " RNG R1 51\n"
                         " RNG R2 52 R3 53\n"
                         "BOUNDS\n"
                         " FR BND X1\n"
                         " FR BND X2\n"
                         " FR BND X3\n"
                         "ENDATA"));
  EXPECT_EQ(driver.context().box().size(), 3);
  const Variable& x1 = driver.context().box().variable(0);
  const Variable& x2 = driver.context().box().variable(1);
  const Variable& x3 = driver.context().box().variable(2);
  EXPECT_EQ(driver.context().assertions().size(), 6u);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(11 * x1 + 31 * x3 >= 1 - 51));
  EXPECT_TRUE(driver.context().assertions()[1].EqualTo(11 * x1 + 31 * x3 <= 1));
  EXPECT_TRUE(driver.context().assertions()[2].EqualTo(12 * x1 + 21 * x2 + 32 * x3 >= 2));
  EXPECT_TRUE(driver.context().assertions()[3].EqualTo(12 * x1 + 21 * x2 + 32 * x3 <= 2 + 52));
  EXPECT_TRUE(driver.context().assertions()[4].EqualTo(33 * x3 >= 3));
  EXPECT_TRUE(driver.context().assertions()[5].EqualTo(33 * x3 <= 3 + 53));
}

TEST_F(TestMpsDriver, RangeNegative) {
  MpsDriver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("ROWS\n"
                         " L  R1\n"
                         " G  R2\n"
                         " E  R3\n"
                         " N  Ob\n"
                         "COLUMNS\n"
                         " X1 R1 11 R2 12.0 \n"
                         " X2 R2 21.00 \n"
                         " X3 R1 31/1 R2 32 \n"
                         " X3 R3 33 \n"
                         "RHS\n"
                         " R1 1\n"
                         " R2 2 R3 3\n"
                         "RANGES\n"
                         " RNG R1 -51\n"
                         " RNG R2 -52 R3 -53\n"
                         "BOUNDS\n"
                         " FR BND X1\n"
                         " FR BND X2\n"
                         " FR BND X3\n"
                         "ENDATA"));
  EXPECT_EQ(driver.context().box().size(), 3);
  const Variable& x1 = driver.context().box().variable(0);
  const Variable& x2 = driver.context().box().variable(1);
  const Variable& x3 = driver.context().box().variable(2);
  EXPECT_EQ(driver.context().assertions().size(), 6u);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(11 * x1 + 31 * x3 >= 1 - 51));
  EXPECT_TRUE(driver.context().assertions()[1].EqualTo(11 * x1 + 31 * x3 <= 1));
  EXPECT_TRUE(driver.context().assertions()[2].EqualTo(12 * x1 + 21 * x2 + 32 * x3 >= 2));
  EXPECT_TRUE(driver.context().assertions()[3].EqualTo(12 * x1 + 21 * x2 + 32 * x3 <= 2 + 52));
  EXPECT_TRUE(driver.context().assertions()[4].EqualTo(33 * x3 >= 3 - 53));
  EXPECT_TRUE(driver.context().assertions()[5].EqualTo(33 * x3 <= 3));
}

TEST_F(TestMpsDriver, BoundsPositive) {
  MpsDriver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("ROWS\n"
                         " E  R1\n"
                         " N  Ob\n"
                         "COLUMNS\n"
                         " X1 R1 1 \n"
                         " X2 R1 1 \n"
                         " X3 R1 1 \n"
                         " X4 R1 1 \n"
                         " X5 R1 1 \n"
                         "BOUNDS\n"
                         " LO BND X1 61\n"
                         " UP BND X2 62\n"
                         " FX BND X3 63\n"
                         " FR BND X4 64\n"
                         " MI BND X5 65\n"
                         " PL BND X5 66\n"
                         "ENDATA"));
  EXPECT_EQ(driver.context().box().size(), 5);
  const Variable& x1 = driver.context().box().variable(0);
  const Variable& x2 = driver.context().box().variable(1);
  const Variable& x3 = driver.context().box().variable(2);
  const Variable& x4 = driver.context().box().variable(3);
  const Variable& x5 = driver.context().box().variable(4);
  EXPECT_EQ(driver.context().assertions().size(), 6u);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(x1 >= 61));
  EXPECT_TRUE(driver.context().assertions()[1].EqualTo(x2 >= 0));
  EXPECT_TRUE(driver.context().assertions()[2].EqualTo(x2 <= 62));
  EXPECT_TRUE(driver.context().assertions()[3].EqualTo(x3 >= 63));
  EXPECT_TRUE(driver.context().assertions()[4].EqualTo(x3 <= 63));
  EXPECT_TRUE(driver.context().assertions()[5].EqualTo(x1 + x2 + x3 + x4 + x5 == 0));
}

TEST_F(TestMpsDriver, BoundsNegative) {
  MpsDriver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("ROWS\n"
                         " E  R1\n"
                         " N  Ob\n"
                         "COLUMNS\n"
                         " X1 R1 1 \n"
                         " X2 R1 1 \n"
                         " X3 R1 1 \n"
                         " X4 R1 1 \n"
                         " X5 R1 1 \n"
                         "BOUNDS\n"
                         " LO BND X1 -61\n"
                         " UP BND X2 -62\n"
                         " FX BND X3 -63\n"
                         " FR BND X4 -64\n"
                         " MI BND X5 -65\n"
                         " PL BND X5 -66\n"
                         "ENDATA"));
  EXPECT_EQ(driver.context().box().size(), 5);
  const Variable& x1 = driver.context().box().variable(0);
  const Variable& x2 = driver.context().box().variable(1);
  const Variable& x3 = driver.context().box().variable(2);
  const Variable& x4 = driver.context().box().variable(3);
  const Variable& x5 = driver.context().box().variable(4);
  EXPECT_EQ(driver.context().assertions().size(), 5u);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(x1 >= -61));
  EXPECT_TRUE(driver.context().assertions()[1].EqualTo(x2 <= -62));
  EXPECT_TRUE(driver.context().assertions()[2].EqualTo(x3 >= -63));
  EXPECT_TRUE(driver.context().assertions()[3].EqualTo(x3 <= -63));
  EXPECT_TRUE(driver.context().assertions()[4].EqualTo(x1 + x2 + x3 + x4 + x5 == 0));
}

TEST_F(TestMpsDriver, BoundsImplicit) {
  MpsDriver driver{context_};
  ASSERT_TRUE(
      driver.ParseString("ROWS\n"
                         " E  R1\n"
                         " N  Ob\n"
                         "COLUMNS\n"
                         " X1 R1 1 \n"
                         " X2 R1 1 \n"
                         " X3 R1 1 \n"
                         " X4 R1 1 \n"
                         " X5 R1 1 \n"
                         "BOUNDS\n"
                         " FR BND X4\n"
                         " MI BND X5\n"
                         " PL BND X5\n"
                         "ENDATA"));
  EXPECT_EQ(driver.context().box().size(), 5);
  const Variable& x1 = driver.context().box().variable(0);
  const Variable& x2 = driver.context().box().variable(1);
  const Variable& x3 = driver.context().box().variable(2);
  const Variable& x4 = driver.context().box().variable(3);
  const Variable& x5 = driver.context().box().variable(4);
  EXPECT_EQ(driver.context().assertions().size(), 4u);
  EXPECT_TRUE(driver.context().assertions()[0].EqualTo(x1 >= 0));
  EXPECT_TRUE(driver.context().assertions()[1].EqualTo(x2 >= 0));
  EXPECT_TRUE(driver.context().assertions()[2].EqualTo(x3 >= 0));
  EXPECT_TRUE(driver.context().assertions()[3].EqualTo(x1 + x2 + x3 + x4 + x5 == 0));
}
