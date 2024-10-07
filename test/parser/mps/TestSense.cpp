/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gtest/gtest.h>

#include "dlinear/parser/mps/Sense.h"

using dlinear::mps::ParseSense;
using dlinear::mps::Sense;

TEST(TestSense, ParseSense) {
  EXPECT_EQ(ParseSense("L"), Sense::L);
  EXPECT_EQ(ParseSense("E"), Sense::E);
  EXPECT_EQ(ParseSense("G"), Sense::G);
  EXPECT_EQ(ParseSense("N"), Sense::N);
}

TEST(TestSense, ParseSenseCaseInsensitive) {
  EXPECT_EQ(ParseSense("l"), Sense::L);
  EXPECT_EQ(ParseSense("e"), Sense::E);
  EXPECT_EQ(ParseSense("g"), Sense::G);
  EXPECT_EQ(ParseSense("n"), Sense::N);
}

TEST(TestSense, ParseSenseChar) {
  EXPECT_EQ(ParseSense('L'), Sense::L);
  EXPECT_EQ(ParseSense('E'), Sense::E);
  EXPECT_EQ(ParseSense('G'), Sense::G);
  EXPECT_EQ(ParseSense('N'), Sense::N);
}

TEST(TestSense, ParseSenseCharCaseInsensitive) {
  EXPECT_EQ(ParseSense('l'), Sense::L);
  EXPECT_EQ(ParseSense('e'), Sense::E);
  EXPECT_EQ(ParseSense('g'), Sense::G);
  EXPECT_EQ(ParseSense('n'), Sense::N);
}
