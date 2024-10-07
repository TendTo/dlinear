/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#ifdef DLINEAR_ENABLED_SOPLEX
#include <gtest/gtest.h>

#include "dlinear/libs/libsoplex.h"

TEST(TestSoplex, Soplex) {
  soplex::SoPlex soplex;
  EXPECT_NO_THROW(soplex.printVersion());
}
#endif