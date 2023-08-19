/**
 * @file TestSoplex.cpp
 * @author dlinear
 * @date 19 Aug 2023
 * @copyright 2023 dlinear
 */
#include "dlinear/libs/soplex.h"

#include <gtest/gtest.h>

TEST(TestSoplex, TestSoplex) {
  soplex::SoPlex soplex;
  EXPECT_NO_THROW(soplex.printVersion());
}