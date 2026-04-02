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

std::vector<std::string> split(std::stringstream& ss, const char delimiter = '\n') {
  std::vector<std::string> tokens;
  std::string token;
  while (std::getline(ss, token, delimiter)) tokens.push_back(token);
  return tokens;
}

class TestMpsDriver : public ::testing::Test {
 protected:
  std::stringstream ss_;
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_), ::testing::UnorderedElementsAre("(set-logic QF_LRA)", "(check-sat)"));
}

TEST_F(TestMpsDriver, SetConfigOptions2) {
  ASSERT_TRUE(
      driver_.ParseString("* @set-option :precision 0.505\n"
                          "* @set-option :produce-models false\n"
                          "ENDATA"));
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_), ::testing::UnorderedElementsAre("(set-logic QF_LRA)", "(check-sat)"));
}

TEST_F(TestMpsDriver, Rows) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
                          " L  R1\n"
                          " G  R2\n"
                          " E  R3\n"
                          " E  R4\n"  // ignored row
                          " N  Ob\n"  // only used for objective
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_), ::testing::UnorderedElementsAre("(set-logic QF_LRA)",        //
                                                          "(declare-const X4 Real)",   //
                                                          "(declare-const X3 Real)",   //
                                                          "(declare-const X2 Real)",   //
                                                          "(declare-const X1 Real)",   //
                                                          "(assert (>= X4 0))",        //
                                                          "(assert (= (* 3 X3) 0))",   //
                                                          "(assert (>= (* 2 X2) 0))",  //
                                                          "(assert (<= X1 0))",        //
                                                          "(minimize (+ (* 4 X4)))",   //
                                                          "(check-sat)",               //
                                                          "(get-objectives)"));
}

TEST_F(TestMpsDriver, SimpleBoundsPositive) {
  ASSERT_TRUE(
      driver_.ParseString("ROWS\n"
                          " L  R1\n"
                          " G  R2\n"
                          " E  R3\n"
                          " E  R4\n"  // ignored row
                          " N  Ob\n"  // only used for objective
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_), ::testing::UnorderedElementsAre("(set-logic QF_LRA)",         //
                                                          "(declare-const X3 Real)",    //
                                                          "(declare-const X2 Real)",    //
                                                          "(declare-const X1 Real)",    //
                                                          "(assert (= (* 3 X3) 33))",   //
                                                          "(assert (>= (* 2 X2) 22))",  //
                                                          "(assert (<= X1 11))",        //
                                                          "(check-sat)"));
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_), ::testing::UnorderedElementsAre("(set-logic QF_LRA)",             //
                                                          "(declare-const X3 Real)",        //
                                                          "(declare-const X2 Real)",        //
                                                          "(declare-const X1 Real)",        //
                                                          "(assert (= (* (- 3) X3) 33))",   //
                                                          "(assert (>= (* (- 2) X2) 22))",  //
                                                          "(assert (<= (* (- 1) X1) 11))",  //
                                                          "(check-sat)"));
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_),
              ::testing::UnorderedElementsAre("(set-logic QF_LRA)",                                     //
                                              "(declare-const X3 Real)",                                //
                                              "(declare-const X2 Real)",                                //
                                              "(declare-const X1 Real)",                                //
                                              "(assert (= (* 33 X3) 0))",                               //
                                              "(assert (>= (+  (* 12 X1)  (* 21 X2)  (* 32 X3) ) 0))",  //
                                              "(assert (<= (+  (* 11 X1)  (* 31 X3) ) 0))",             //
                                              "(check-sat)"));
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_),
              ::testing::UnorderedElementsAre("(set-logic QF_LRA)",                                     //
                                              "(declare-const X3 Real)",                                //
                                              "(declare-const X2 Real)",                                //
                                              "(declare-const X1 Real)",                                //
                                              "(assert (= (* 33 X3) 3))",                               //
                                              "(assert (>= (+  (* 12 X1)  (* 21 X2)  (* 32 X3) ) 2))",  //
                                              "(assert (<= (+  (* 11 X1)  (* 31 X3) ) 1))",             //
                                              "(check-sat)"));
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_),
              ::testing::UnorderedElementsAre("(set-logic QF_LRA)",                                      //
                                              "(declare-const X3 Real)",                                 //
                                              "(declare-const X2 Real)",                                 //
                                              "(declare-const X1 Real)",                                 //
                                              "(assert (>= (* 33 X3) 3))",                               //
                                              "(assert (<= (* 33 X3) 56))",                              //
                                              "(assert (>= (+  (* 12 X1)  (* 21 X2)  (* 32 X3) ) 2))",   //
                                              "(assert (<= (+  (* 12 X1)  (* 21 X2)  (* 32 X3) ) 54))",  //
                                              "(assert (>= (+  (* 11 X1)  (* 31 X3) ) (- 50)))",         //
                                              "(assert (<= (+  (* 11 X1)  (* 31 X3) ) 1))",              //
                                              "(check-sat)"));
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_),
              ::testing::UnorderedElementsAre("(set-logic QF_LRA)",                                      //
                                              "(declare-const X3 Real)",                                 //
                                              "(declare-const X2 Real)",                                 //
                                              "(declare-const X1 Real)",                                 //
                                              "(assert (>= (* 33 X3) (- 50)))",                          //
                                              "(assert (<= (* 33 X3) 3))",                               //
                                              "(assert (>= (+  (* 12 X1)  (* 21 X2)  (* 32 X3) ) 2))",   //
                                              "(assert (<= (+  (* 12 X1)  (* 21 X2)  (* 32 X3) ) 54))",  //
                                              "(assert (>= (+  (* 11 X1)  (* 31 X3) ) (- 50)))",         //
                                              "(assert (<= (+  (* 11 X1)  (* 31 X3) ) 1))",              //
                                              "(check-sat)"));
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_), ::testing::UnorderedElementsAre("(set-logic QF_LRA)",                       //
                                                          "(declare-const X5 Real)",                  //
                                                          "(declare-const X4 Real)",                  //
                                                          "(declare-const X3 Real)",                  //
                                                          "(declare-const X2 Real)",                  //
                                                          "(declare-const X1 Real)",                  //
                                                          "(assert (= X3 63))",                       //
                                                          "(assert (>= X2 0))",                       //
                                                          "(assert (<= X2 62))",                      //
                                                          "(assert (>= X1 61))",                      //
                                                          "(assert (= (+  X1  X2  X3  X4  X5 ) 0))",  //
                                                          "(check-sat)"));
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_), ::testing::UnorderedElementsAre("(set-logic QF_LRA)",                       //
                                                          "(declare-const X5 Real)",                  //
                                                          "(declare-const X4 Real)",                  //
                                                          "(declare-const X3 Real)",                  //
                                                          "(declare-const X2 Real)",                  //
                                                          "(declare-const X1 Real)",                  //
                                                          "(assert (= X3 (- 63)))",                   //
                                                          "(assert (<= X2 (- 62)))",                  //
                                                          "(assert (>= X1 (- 61)))",                  //
                                                          "(assert (= (+  X1  X2  X3  X4  X5 ) 0))",  //
                                                          "(check-sat)"));
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_), ::testing::UnorderedElementsAre("(set-logic QF_LRA)",                       //
                                                          "(declare-const X5 Real)",                  //
                                                          "(declare-const X4 Real)",                  //
                                                          "(declare-const X3 Real)",                  //
                                                          "(declare-const X2 Real)",                  //
                                                          "(declare-const X1 Real)",                  //
                                                          "(assert (>= X3 0))",                       //
                                                          "(assert (>= X2 0))",                       //
                                                          "(assert (>= X1 0))",                       //
                                                          "(assert (= (+  X1  X2  X3  X4  X5 ) 0))",  //
                                                          "(check-sat)"));
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_), ::testing::UnorderedElementsAre("(set-logic QF_LRA)",                           //
                                                          "(declare-const X6 Real)",                      //
                                                          "(declare-const X5 Real)",                      //
                                                          "(declare-const X4 Real)",                      //
                                                          "(declare-const X3 Real)",                      //
                                                          "(declare-const X2 Real)",                      //
                                                          "(declare-const X1 Real)",                      //
                                                          "(assert (>= X6 0))",                           //
                                                          "(assert (<= X5 (- 1)))",                       //
                                                          "(assert (>= X4 0))",                           //
                                                          "(assert (<= X4 10))",                          //
                                                          "(assert (>= X3 0))",                           //
                                                          "(assert (<= X3 1))",                           //
                                                          "(assert (>= X2 (- 10)))",                      //
                                                          "(assert (<= X2 1))",                           //
                                                          "(assert (>= X1 0))",                           //
                                                          "(assert (= (+  X1  X2  X3  X4  X5  X6 ) 0))",  //
                                                          "(check-sat)"));
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_), ::testing::UnorderedElementsAre("(set-logic QF_LRA)",                           //
                                                          "(declare-const X6 Real)",                      //
                                                          "(declare-const X5 Real)",                      //
                                                          "(declare-const X4 Real)",                      //
                                                          "(declare-const X3 Real)",                      //
                                                          "(declare-const X2 Real)",                      //
                                                          "(declare-const X1 Real)",                      //
                                                          "(assert (>= X6 0))",                           //
                                                          "(assert (<= X5 (- 1)))",                       //
                                                          "(assert (>= X4 0))",                           //
                                                          "(assert (<= X4 10))",                          //
                                                          "(assert (>= X3 0))",                           //
                                                          "(assert (<= X3 1))",                           //
                                                          "(assert (>= X2 (- 10)))",                      //
                                                          "(assert (>= X1 0))",                           //
                                                          "(assert (= (+  X1  X2  X3  X4  X5  X6 ) 0))",  //
                                                          "(check-sat)"));
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_),
              ::testing::UnorderedElementsAre("(set-logic QF_LRA)",                                   //
                                              "(declare-const X8 Real)",                              //
                                              "(declare-const X7 Real)",                              //
                                              "(declare-const X6 Real)",                              //
                                              "(declare-const X5 Real)",                              //
                                              "(declare-const X4 Real)",                              //
                                              "(declare-const X3 Real)",                              //
                                              "(declare-const X2 Real)",                              //
                                              "(declare-const X1 Real)",                              //
                                              "(assert (>= X8 1))",                                   //
                                              "(assert (>= X7 (- 1)))",                               //
                                              "(assert (>= X6 1))",                                   //
                                              "(assert (>= X5 (- 1)))",                               //
                                              "(assert (>= X4 1))",                                   //
                                              "(assert (>= X3 (- 1)))",                               //
                                              "(assert (= X2 1))",                                    //
                                              "(assert (>= X1 (- 1)))",                               //
                                              "(assert (<= X1 1))",                                   //
                                              "(assert (= (+  X1  X2  X3  X4  X5  X6  X7  X8 ) 0))",  //
                                              "(check-sat)"));
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_),
              ::testing::UnorderedElementsAre("(set-logic QF_LRA)",                                   //
                                              "(declare-const X8 Real)",                              //
                                              "(declare-const X7 Real)",                              //
                                              "(declare-const X6 Real)",                              //
                                              "(declare-const X5 Real)",                              //
                                              "(declare-const X4 Real)",                              //
                                              "(declare-const X3 Real)",                              //
                                              "(declare-const X2 Real)",                              //
                                              "(declare-const X1 Real)",                              //
                                              "(assert (>= X8 0))",                                   //
                                              "(assert (<= X8 2))",                                   //
                                              "(assert (<= X7 (- 2)))",                               //
                                              "(assert (>= X6 0))",                                   //
                                              "(assert (<= X6 2))",                                   //
                                              "(assert (<= X5 (- 2)))",                               //
                                              "(assert (>= X4 0))",                                   //
                                              "(assert (<= X4 2))",                                   //
                                              "(assert (<= X3 (- 2)))",                               //
                                              "(assert (>= X2 0))",                                   //
                                              "(assert (<= X2 2))",                                   //
                                              "(assert (<= X1 (- 2)))",                               //
                                              "(assert (= (+  X1  X2  X3  X4  X5  X6  X7  X8 ) 0))",  //
                                              "(check-sat)"));
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
  driver_.ToSmt2(ss_);
  EXPECT_THAT(split(ss_), ::testing::UnorderedElementsAre("(set-logic QF_LRA)",       //
                                                          "(declare-const X1 Real)",  //
                                                          "(assert (>= X1 0))",       //
                                                          "(assert (<= X1 4))",       //
                                                          "(assert (>= X1 (- 3)))",   //
                                                          "(assert (<= X1 0))",       //
                                                          "(assert (>= X1 0))",       //
                                                          "(assert (<= X1 2))",       //
                                                          "(assert (>= X1 (- 1)))",   //
                                                          "(assert (<= X1 0))",       //
                                                          "(minimize (+ X1))",        //
                                                          "(check-sat)",              //
                                                          "(get-objectives)"));
}
