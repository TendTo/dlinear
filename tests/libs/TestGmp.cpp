/**
 * @file TestGmp.cpp
 * @author dlinear
 * @date 19 Aug 2023
 * @copyright 2023 dlinear
 */
#include "dlinear/libs/gmp.h"

#include <gtest/gtest.h>

using dlinear::gmp::floor;
using dlinear::gmp::ceil;
using dlinear::gmp::to_mpq_class;
using dlinear::gmp::to_mpq_t;

TEST(TestGmp, TestFloorFractions) {
  EXPECT_EQ(floor(mpq_class{1, 2}), 0);
  EXPECT_EQ(floor(mpq_class{3, 2}), 1);
  EXPECT_EQ(floor(mpq_class{7, 3}), 2);
  EXPECT_EQ(floor(mpq_class{-1, 2}), -1);
  EXPECT_EQ(floor(mpq_class{-3, 2}), -2);
  EXPECT_EQ(floor(mpq_class{-7, 3}), -3);
}

TEST(TestGmp, TestFloorIntegers) {
  EXPECT_EQ(floor(mpq_class{1}), 1);
  EXPECT_EQ(floor(mpq_class{-1}), -1);
  EXPECT_EQ(floor(mpq_class{0}), 0);
}

TEST(TestGmp, TestCeilFractions) {
  EXPECT_EQ(ceil(mpq_class{1, 2}), 1);
  EXPECT_EQ(ceil(mpq_class{3, 2}), 2);
  EXPECT_EQ(ceil(mpq_class{7, 3}), 3);
  EXPECT_EQ(ceil(mpq_class{-1, 2}), 0);
  EXPECT_EQ(ceil(mpq_class{-3, 2}), -1);
  EXPECT_EQ(ceil(mpq_class{-7, 3}), -2);
}

TEST(TestGmp, TestCeilIntegers) {
  EXPECT_EQ(ceil(mpq_class{1}), 1);
  EXPECT_EQ(ceil(mpq_class{-1}), -1);
  EXPECT_EQ(ceil(mpq_class{0}), 0);
}

TEST(TestGmp, TestToMpqClass) {
  mpq_t a;
  mpq_init(a);

  mpq_set_d(a, 1);
  EXPECT_EQ(to_mpq_class(a), mpq_class{1});

  mpq_set_d(a, 0);
  EXPECT_EQ(to_mpq_class(a), mpq_class{0});

  mpq_set_si(a, 1, 2);
  EXPECT_EQ(to_mpq_class(a), mpq_class(1, 2));

  mpq_clear(a);
}

TEST(TestGmp, TestToMpqT) {
  mpq_class a{1};
  mpq_t b;
  mpq_init(b);

  mpq_set_d(b, 1);
  EXPECT_TRUE(mpq_equal(to_mpq_t(a), b));

  a = 0;
  mpq_set_d(b, 0);
  EXPECT_TRUE(mpq_equal(to_mpq_t(a), b));

  a = mpq_class{1, 2};
  mpq_set_si(b, 1, 2);
  EXPECT_TRUE(mpq_equal(to_mpq_t(a), b));

  mpq_clear(b);
}