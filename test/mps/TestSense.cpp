/**
 * @file TestSense.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include "dlinear/mps/Sense.h"

using dlinear::mps::Sense;
using dlinear::mps::ParseSense;

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
