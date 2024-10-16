/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gtest/gtest.h>

#include <limits>
#include <stdexcept>

#include "dlinear/util/math.h"

using dlinear::ConvertInt64ToDouble;
using dlinear::ConvertInt64ToInt;
using dlinear::IsInteger;
using std::int64_t;
using std::numeric_limits;
using std::runtime_error;

TEST(TestMath, IsInteger) {
  EXPECT_TRUE(IsInteger(3.0));
  EXPECT_FALSE(IsInteger(3.1));
}

TEST(TestMath, ConvertInt64ToInt) {
  EXPECT_EQ(ConvertInt64ToInt(3017294L), 3017294);
  EXPECT_THROW(ConvertInt64ToInt(numeric_limits<int>::max() + 1L), runtime_error);
  EXPECT_THROW(ConvertInt64ToInt(numeric_limits<int>::min() - 1L), runtime_error);
}

TEST(TestMath, ConvertInt64ToDouble) {
  EXPECT_EQ(ConvertInt64ToDouble(3017294L), 3017294.0);
  constexpr int64_t m1{1UL << numeric_limits<double>::digits};
  constexpr double m2{1UL << numeric_limits<double>::digits};

  EXPECT_EQ(ConvertInt64ToDouble(m1), m2);
  EXPECT_THROW(ConvertInt64ToDouble(m1 + 1), runtime_error);
  EXPECT_THROW(ConvertInt64ToDouble(-m1 - 1), runtime_error);
}