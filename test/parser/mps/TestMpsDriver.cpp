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
  MpsDriver driver_{context_};

  const Variable& x(const int idx, const bool doNotSub = false) const {
    return context_.box().variable(idx - !doNotSub);
  }
};

MATCHER(FEq, "Check structural equality between two formulas") { return std::get<0>(arg).EqualTo(std::get<1>(arg)); }

TEST_F(TestMpsDriver, SetConfigOptions1) {
  ASSERT_TRUE(
      driver_.ParseString("* @set-option :precision 1\n"
                          "* @set-option :produce-models true\n"
                          "ENDATA"));
  EXPECT_EQ(driver_.context().config().precision(), 1);
  EXPECT_TRUE(driver_.context().config().produce_models());
}

TEST_F(TestMpsDriver, SetConfigOptions2) {
  ASSERT_TRUE(
      driver_.ParseString("* @set-option :precision 0.505\n"
                          "* @set-option :produce-models false\n"
                          "ENDATA"));
  EXPECT_EQ(driver_.context().config().precision(), 0.505);
  EXPECT_FALSE(driver_.context().config().produce_models());
}

TEST_F(TestMpsDriver, Name) {
  ASSERT_TRUE(
      driver_.ParseString("NAME best name ever\n"
                          "ENDATA"));
  EXPECT_EQ(driver_.problem_name(), "best name ever");
}

TEST_F(TestMpsDriver, Rows) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
                          " L  R1\n"
                          " G  R2\n"
                          " E  R3\n"
                          " E  R4\n"  // ignored row
                          " N  Ob\n"  // only used for  objective
                          "COLUMNS\n"
                          " X1 R1 1.\n"
                          " X2 R2 2.\n"
                          " X3 R3 3.\n"
                          " X4 Ob 4.\n"
                          "BOUNDS\n"
                          " FR BND X1\n"
                          " FR BND X2\n"
                          " FR BND X3\n"
                          "ENDATA"));
  ASSERT_EQ(driver_.context().box().size(), 4u);
  EXPECT_THAT(driver_.context().assertions(), ::testing::UnorderedPointwise(FEq(), {x(1) <= 0,      //
                                                                                    2 * x(2) >= 0,  //
                                                                                    3 * x(3) == 0,  //
                                                                                    x(4) >= 0}));
}

TEST_F(TestMpsDriver, SimpleBoundsPositive) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
                          " L  R1\n"
                          " G  R2\n"
                          " E  R3\n"
                          " E  R4\n"  // ignored row
                          " N  Ob\n"  // only used for  objective
                          "COLUMNS\n"
                          " X1 R1 1.\n"
                          " X2 R2 2.\n"
                          " X3 R3 3.\n"
                          "BOUNDS\n"
                          " FR BND X1\n"
                          " FR BND X2\n"
                          " FR BND X3\n"
                          "RHS\n"
                          " R1 11\n"
                          " R2 22 R3 33\n"
                          "ENDATA"));
  ASSERT_EQ(driver_.context().box().size(), 3u);

  EXPECT_THAT(driver_.context().assertions(), ::testing::UnorderedPointwise(FEq(), {x(1) <= 11,      //
                                                                                    2 * x(2) >= 22,  //
                                                                                    3 * x(3) == 33}));
}

TEST_F(TestMpsDriver, SimpleBoundsNegative) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
                          " L  R1\n"
                          " G  R2\n"
                          " E  R3\n"
                          " E  R4\n"  // ignored row
                          " N  Ob\n"  // only used for  objective
                          "COLUMNS\n"
                          " X1 R1 -1.\n"
                          " X2 R2 -2.\n"
                          " X3 R3 -3.\n"
                          "BOUNDS\n"
                          " FR BND X1\n"
                          " FR BND X2\n"
                          " FR BND X3\n"
                          "RHS\n"
                          " R1 11\n"
                          " R2 22 R3 33\n"
                          "ENDATA"));
  ASSERT_EQ(driver_.context().box().size(), 3u);

  EXPECT_THAT(driver_.context().assertions(), ::testing::UnorderedPointwise(FEq(), {-1 * x(1) <= 11,  //
                                                                                    -2 * x(2) >= 22,  //
                                                                                    -3 * x(3) == 33}));
}

TEST_F(TestMpsDriver, Columns) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
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
  ASSERT_EQ(driver_.context().box().size(), 3u);

  EXPECT_THAT(driver_.context().assertions(),
              ::testing::UnorderedPointwise(FEq(), {11 * x(1) + 31 * x(3) <= 0,              //
                                                    12 * x(1) + 21 * x(2) + 32 * x(3) >= 0,  //
                                                    33 * x(3) == 0}));
}

TEST_F(TestMpsDriver, Rhs) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
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
  ASSERT_EQ(driver_.context().box().size(), 3u);

  EXPECT_THAT(driver_.context().assertions(),
              ::testing::UnorderedPointwise(FEq(), {11 * x(1) + 31 * x(3) <= 1,              //
                                                    12 * x(1) + 21 * x(2) + 32 * x(3) >= 2,  //
                                                    33 * x(3) == 3}));
}

TEST_F(TestMpsDriver, RangePositive) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
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
  ASSERT_EQ(driver_.context().box().size(), 3u);

  EXPECT_THAT(driver_.context().assertions(),
              ::testing::UnorderedPointwise(FEq(), {11 * x(1) + 31 * x(3) >= 1 - 51,              //
                                                    11 * x(1) + 31 * x(3) <= 1,                   //
                                                    12 * x(1) + 21 * x(2) + 32 * x(3) >= 2,       //
                                                    12 * x(1) + 21 * x(2) + 32 * x(3) <= 2 + 52,  //
                                                    33 * x(3) >= 3,                               //
                                                    33 * x(3) <= 3 + 53}));
}

TEST_F(TestMpsDriver, RangeNegative) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
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
  ASSERT_EQ(driver_.context().box().size(), 3u);

  EXPECT_THAT(driver_.context().assertions(),
              ::testing::UnorderedPointwise(FEq(), {11 * x(1) + 31 * x(3) >= 1 - 51,              //
                                                    11 * x(1) + 31 * x(3) <= 1,                   //
                                                    12 * x(1) + 21 * x(2) + 32 * x(3) >= 2,       //
                                                    12 * x(1) + 21 * x(2) + 32 * x(3) <= 2 + 52,  //
                                                    33 * x(3) >= 3 - 53,                          //
                                                    33 * x(3) <= 3}));
}

TEST_F(TestMpsDriver, BoundsPositive) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
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
  ASSERT_EQ(driver_.context().box().size(), 5u);

  EXPECT_THAT(driver_.context().assertions(),
              ::testing::UnorderedPointwise(FEq(), {x(1) >= 61,  //
                                                    x(2) >= 0,   //
                                                    x(2) <= 62,  //
                                                    x(3) == 63,  //
                                                    x(1) + x(2) + x(3) + x(4) + x(5) == 0}));
}

TEST_F(TestMpsDriver, BoundsNegative) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
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
  ASSERT_EQ(driver_.context().box().size(), 5u);

  EXPECT_THAT(driver_.context().assertions(),
              ::testing::UnorderedPointwise(FEq(), {x(1) >= -61,  //
                                                    x(2) <= -62,  //
                                                    x(3) == -63,  //
                                                    x(1) + x(2) + x(3) + x(4) + x(5) == 0}));
}

TEST_F(TestMpsDriver, BoundsImplicit) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
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
  ASSERT_EQ(driver_.context().box().size(), 5u);

  EXPECT_THAT(driver_.context().assertions(),
              ::testing::UnorderedPointwise(FEq(), {x(1) >= 0,  //
                                                    x(2) >= 0,  //
                                                    x(3) >= 0,  //
                                                    x(1) + x(2) + x(3) + x(4) + x(5) == 0}));
}

TEST_F(TestMpsDriver, BoundsIntegerImplicit) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
                          " E  R1\n"
                          " N  Ob\n"
                          "COLUMNS\n"
                          " X1 R1 1 \n"
                          " Mark 'MARKER' 'INTORG'\n"
                          " X2 R1 1 \n"
                          " X3 R1 1 \n"
                          " X4 R1 1 \n"
                          " X5 R1 1 \n"
                          " Mark 'MARKER' 'INTEND'\n"
                          " X6 R1 1 \n"
                          "BOUNDS\n"
                          " LO BND X2 -10\n"
                          " UP BND X4 10\n"
                          " UP BND X5 -1\n"
                          "ENDATA"));
  ASSERT_EQ(driver_.context().box().size(), 6u);

  EXPECT_THAT(driver_.context().assertions(),
              ::testing::UnorderedPointwise(FEq(), {x(1) >= 0,    //
                                                    x(2) >= -10,  //
                                                    x(2) <= 1,    //
                                                    x(3) >= 0,    //
                                                    x(3) <= 1,    //
                                                    x(4) >= 0,    //
                                                    x(4) <= 10,   //
                                                    x(5) <= -1,   //
                                                    x(6) >= 0,    //
                                                    x(1) + x(2) + x(3) + x(4) + x(5) + x(6) == 0}));
}

TEST_F(TestMpsDriver, BoundsIntegerImplicitOnBounds) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
                          " E  R1\n"
                          " N  Ob\n"
                          "COLUMNS\n"
                          " X1 R1 1 \n"
                          " X2 R1 1 \n"
                          " Mark 'MARKER' 'INTORG'\n"
                          " X3 R1 1 \n"
                          " X4 R1 1 \n"
                          " Mark 'MARKER' 'INTEND'\n"
                          " X5 R1 1 \n"
                          " X6 R1 1 \n"
                          "BOUNDS\n"
                          " LI BND X2 -10\n"
                          " UP BND X4 10\n"
                          " UI BND X5 -1\n"
                          "ENDATA"));
  ASSERT_EQ(driver_.context().box().size(), 6u);

  EXPECT_THAT(driver_.context().assertions(),
              ::testing::UnorderedPointwise(FEq(), {x(1) >= 0,    //
                                                    x(2) >= -10,  //
                                                    x(3) >= 0,    //
                                                    x(3) <= 1,    //
                                                    x(4) >= 0,    //
                                                    x(4) <= 10,   //
                                                    x(5) <= -1,   //
                                                    x(6) >= 0,    //
                                                    x(1) + x(2) + x(3) + x(4) + x(5) + x(6) == 0}));
}

TEST_F(TestMpsDriver, BoundsLower) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
                          " E  R1\n"
                          " N  Ob\n"
                          "COLUMNS\n"
                          " Mark 'MARKER' 'INTORG'\n"
                          " X1 R1 1 \n"
                          " X2 R1 1 \n"
                          " X3 R1 1 \n"
                          " X4 R1 1 \n"
                          " Mark 'MARKER' 'INTEND'\n"
                          " X5 R1 1 \n"
                          " X6 R1 1 \n"
                          " X7 R1 1 \n"
                          " X8 R1 1 \n"
                          "BOUNDS\n"
                          " LO BND X1 -1\n"
                          " LO BND X2 1\n"
                          " LI BND X3 -1\n"
                          " LI BND X4 1\n"
                          " LO BND X5 -1\n"
                          " LO BND X6 1\n"
                          " LI BND X7 -1\n"
                          " LI BND X8 1\n"
                          "ENDATA"));
  ASSERT_EQ(driver_.context().box().size(), 8u);

  EXPECT_THAT(driver_.context().assertions(),
              ::testing::UnorderedPointwise(FEq(), {x(1) >= -1,  //
                                                    x(1) <= 1,   //
                                                    x(2) == 1,   //
                                                    x(3) >= -1,  //
                                                    x(4) >= 1,   //
                                                    x(5) >= -1,  //
                                                    x(6) >= 1,   //
                                                    x(7) >= -1,  //
                                                    x(8) >= 1,   //
                                                    x(1) + x(2) + x(3) + x(4) + x(5) + x(6) + x(7) + x(8) == 0}));
}

TEST_F(TestMpsDriver, BoundsUpper) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
                          " E  R1\n"
                          " N  Ob\n"
                          "COLUMNS\n"
                          " Mark 'MARKER' 'INTORG'\n"
                          " X1 R1 1 \n"
                          " X2 R1 1 \n"
                          " X3 R1 1 \n"
                          " X4 R1 1 \n"
                          " Mark 'MARKER' 'INTEND'\n"
                          " X5 R1 1 \n"
                          " X6 R1 1 \n"
                          " X7 R1 1 \n"
                          " X8 R1 1 \n"
                          "BOUNDS\n"
                          " UP BND X1 -2\n"
                          " UP BND X2 2\n"
                          " UI BND X3 -2\n"
                          " UI BND X4 2\n"
                          " UP BND X5 -2\n"
                          " UP BND X6 2\n"
                          " UI BND X7 -2\n"
                          " UI BND X8 2\n"
                          "ENDATA"));
  ASSERT_EQ(driver_.context().box().size(), 8u);

  EXPECT_THAT(driver_.context().assertions(),
              ::testing::UnorderedPointwise(FEq(), {x(1) <= -2,  //
                                                    x(2) <= 2,   //
                                                    x(2) >= 0,   //
                                                    x(3) <= -2,  //
                                                    x(4) <= 2,   //
                                                    x(4) >= 0,   //
                                                    x(5) <= -2,  //
                                                    x(6) <= 2,   //
                                                    x(6) >= 0,   //
                                                    x(7) <= -2,  //
                                                    x(8) <= 2,   //
                                                    x(8) >= 0,   //
                                                    x(1) + x(2) + x(3) + x(4) + x(5) + x(6) + x(7) + x(8) == 0}));
}

TEST_F(TestMpsDriver, RangesDefaultRhs) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
                          " L  R1\n"
                          " E  R2\n"
                          " E  R3\n"
                          " G  R4\n"
                          " N  Ob\n"
                          "COLUMNS\n"
                          " X1 R1 1 \n"
                          " X1 R2 1 \n"
                          " X1 R3 1 \n"
                          " X1 R4 1 \n"
                          " X1 Ob 1 \n"
                          "BOUNDS\n"
                          " FR BND X1\n"
                          "RANGES\n"
                          " RNG R1 1\n"
                          " RNG R2 2\n"
                          " RNG R3 -3\n"
                          " RNG R4 4\n"
                          "ENDATA"));
  ASSERT_EQ(driver_.context().box().size(), 1u);

  EXPECT_THAT(driver_.context().assertions(), ::testing::UnorderedPointwise(FEq(), {x(1) <= 0,   //
                                                                                    x(1) >= -1,  //
                                                                                    x(1) <= 2,   //
                                                                                    x(1) >= 0,   //
                                                                                    x(1) >= -3,  //
                                                                                    x(1) <= 0,   //
                                                                                    x(1) >= 0,   //
                                                                                    x(1) <= 4}));
}
