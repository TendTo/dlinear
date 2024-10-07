/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gtest/gtest.h>

#include "dlinear/parser/mps/BoundType.h"

using dlinear::mps::BoundType;
using dlinear::mps::ParseBoundType;

TEST(TestBoundType, ParseBoundType) {
  EXPECT_EQ(ParseBoundType("LO"), BoundType::LO);
  EXPECT_EQ(ParseBoundType("LI"), BoundType::LI);
  EXPECT_EQ(ParseBoundType("UP"), BoundType::UP);
  EXPECT_EQ(ParseBoundType("UI"), BoundType::UI);
  EXPECT_EQ(ParseBoundType("FX"), BoundType::FX);
  EXPECT_EQ(ParseBoundType("FR"), BoundType::FR);
  EXPECT_EQ(ParseBoundType("MI"), BoundType::MI);
  EXPECT_EQ(ParseBoundType("PL"), BoundType::PL);
  EXPECT_EQ(ParseBoundType("BV"), BoundType::BV);
}

TEST(TestBoundType, ParseBoundTypeCaseInsensitive) {
  EXPECT_EQ(ParseBoundType("lo"), BoundType::LO);
  EXPECT_EQ(ParseBoundType("Lo"), BoundType::LO);
  EXPECT_EQ(ParseBoundType("Lo"), BoundType::LO);
  EXPECT_EQ(ParseBoundType("LO"), BoundType::LO);
}
