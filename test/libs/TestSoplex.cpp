/**
 * @file TestSoplex.cpp
 * @author dlinear
 * @date 19 Aug 2023
 * @copyright 2023 dlinear
 */
#ifdef DLINEAR_ENABLED_SOPLEX
#include <gtest/gtest.h>

#include "dlinear/libs/soplex.h"

TEST(TestSoplex, Soplex) {
  soplex::SoPlex soplex;
  EXPECT_NO_THROW(soplex.printVersion());
}
#endif