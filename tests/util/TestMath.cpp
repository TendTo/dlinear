/**
 * @file TestMath.cpp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 */

#include "dlinear/util/math.h"

#include <gtest/gtest.h>
#include <limits>
#include <stdexcept>

using std::int64_t;
using std::numeric_limits;
using std::runtime_error;
using dlinear::convert_int64_to_double;
using dlinear::convert_int64_to_int;
using dlinear::is_integer;

TEST(TestMath, IsInteger) {
  EXPECT_TRUE(is_integer(3.0));
  EXPECT_FALSE(is_integer(3.1));
}

TEST(TestMath, ConvertInt64ToInt) {
  EXPECT_EQ(convert_int64_to_int(3017294L), 3017294);
  EXPECT_THROW(convert_int64_to_int(numeric_limits<int>::max() + 1L),
               runtime_error);
  EXPECT_THROW(convert_int64_to_int(numeric_limits<int>::min() - 1L),
               runtime_error);
}

TEST(TestMath, ConvertInt64ToDouble) {
  EXPECT_EQ(convert_int64_to_double(3017294L), 3017294.0);
  constexpr int64_t m1{1UL << numeric_limits<double>::digits};
  constexpr double m2{1UL << numeric_limits<double>::digits};

  EXPECT_EQ(convert_int64_to_double(m1), m2);
  EXPECT_THROW(convert_int64_to_double(m1 + 1), runtime_error);
  EXPECT_THROW(convert_int64_to_double(-m1 - 1), runtime_error);
}