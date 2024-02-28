/**
 * @file TestSoplex.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#ifdef DLINEAR_ENABLED_SOPLEX
#include <gtest/gtest.h>

#include "dlinear/libs/soplex.h"

TEST(TestSoplex, Soplex) {
  soplex::SoPlex soplex;
  EXPECT_NO_THROW(soplex.printVersion());
}
#endif