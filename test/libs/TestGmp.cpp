/**
 * @file TestGmp.cpp
 * @author dlinear
 * @date 19 Aug 2023
 * @copyright 2023 dlinear
 */
#include <gtest/gtest.h>

#include "dlinear/libs/gmp.h"

using dlinear::gmp::ceil;
using dlinear::gmp::floor;
using dlinear::gmp::string_to_mpq;
using dlinear::gmp::to_mpq_class;
using dlinear::gmp::to_mpq_t;
using std::make_pair;

class TestGmp : public ::testing::TestWithParam<std::pair<std::string, mpq_class>> {};

INSTANTIATE_TEST_SUITE_P(TestGmp, TestGmp,
                         ::testing::Values(make_pair("0", mpq_class{0}), make_pair(".", mpq_class{0}),
                                           make_pair("0.", mpq_class{0}), make_pair("0.0", mpq_class{0}),
                                           make_pair(".0", mpq_class{0}), make_pair("15", mpq_class{15}),
                                           make_pair("1.5", mpq_class{15, 10}), make_pair("0000015.", mpq_class{15}),
                                           make_pair(".15", mpq_class{15, 100}), make_pair(".15", mpq_class{15, 100}),
                                           make_pair(".0015", mpq_class{15, 10000}), make_pair("15.0", mpq_class{15}),
                                           make_pair("15.00", mpq_class{15}), make_pair("0150", mpq_class{150}),
                                           make_pair("1.5E2", mpq_class{150}), make_pair("1.5E-2", mpq_class{15, 1000}),
                                           make_pair(".e+2", mpq_class{0}), make_pair(".5E+2", mpq_class{50}),
                                           make_pair("000000.5E+2", mpq_class{50}),
                                           make_pair("000000.005E-2", mpq_class{5, 100000}),
                                           make_pair("E+2", mpq_class{100}), make_pair("7E+2", mpq_class{700}),
                                           make_pair("E-2", mpq_class{1, 100}), make_pair("15/6", mpq_class{15, 6}),
                                           make_pair("0/1010", mpq_class{0})));

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

TEST_P(TestGmp, TesConvertStringToMpq) {
  auto [s, expected] = GetParam();
  expected.canonicalize();
  EXPECT_EQ(string_to_mpq(s), expected);
}

TEST_P(TestGmp, TesConvertStringToMpqPrefixPlus) {
  auto [s, expected] = GetParam();
  expected.canonicalize();
  EXPECT_EQ(string_to_mpq("+" + s), expected);
}

TEST_P(TestGmp, TesConvertStringToMpqPrefixMinus) {
  auto [s, expected] = GetParam();
  expected.canonicalize();
  EXPECT_EQ(string_to_mpq("-" + s), -expected);
}