/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gtest/gtest.h>

#include "dlinear/libs/libgmp.h"

using dlinear::gmp::ceil;
using dlinear::gmp::floor;
using dlinear::gmp::StringToMpq;
using dlinear::gmp::ToMpq;
using dlinear::gmp::ToMpqClass;
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

TEST(TestGmp, FloorFractions) {
  EXPECT_EQ(floor(mpq_class{1, 2}), 0);
  EXPECT_EQ(floor(mpq_class{3, 2}), 1);
  EXPECT_EQ(floor(mpq_class{7, 3}), 2);
  EXPECT_EQ(floor(mpq_class{-1, 2}), -1);
  EXPECT_EQ(floor(mpq_class{-3, 2}), -2);
  EXPECT_EQ(floor(mpq_class{-7, 3}), -3);
}

TEST(TestGmp, FloorIntegers) {
  EXPECT_EQ(floor(mpq_class{1}), 1);
  EXPECT_EQ(floor(mpq_class{-1}), -1);
  EXPECT_EQ(floor(mpq_class{0}), 0);
}

TEST(TestGmp, CeilFractions) {
  EXPECT_EQ(ceil(mpq_class{1, 2}), 1);
  EXPECT_EQ(ceil(mpq_class{3, 2}), 2);
  EXPECT_EQ(ceil(mpq_class{7, 3}), 3);
  EXPECT_EQ(ceil(mpq_class{-1, 2}), 0);
  EXPECT_EQ(ceil(mpq_class{-3, 2}), -1);
  EXPECT_EQ(ceil(mpq_class{-7, 3}), -2);
}

TEST(TestGmp, CeilIntegers) {
  EXPECT_EQ(ceil(mpq_class{1}), 1);
  EXPECT_EQ(ceil(mpq_class{-1}), -1);
  EXPECT_EQ(ceil(mpq_class{0}), 0);
}

TEST(TestGmp, ToMpqClass) {
  mpq_t a;
  mpq_init(a);

  mpq_set_d(a, 1);
  EXPECT_EQ(ToMpqClass(a), mpq_class{1});

  mpq_set_d(a, 0);
  EXPECT_EQ(ToMpqClass(a), mpq_class{0});

  mpq_set_si(a, 1, 2);
  EXPECT_EQ(ToMpqClass(a), mpq_class(1, 2));

  mpq_clear(a);
}

TEST(TestGmp, ToMpqT) {
  mpq_class a{1};
  mpq_t b;
  mpq_init(b);

  mpq_set_d(b, 1);
  EXPECT_TRUE(mpq_equal(ToMpq(a), b));

  a = 0;
  mpq_set_d(b, 0);
  EXPECT_TRUE(mpq_equal(ToMpq(a), b));

  a = mpq_class{1, 2};
  mpq_set_si(b, 1, 2);
  EXPECT_TRUE(mpq_equal(ToMpq(a), b));

  mpq_clear(b);
}

TEST_P(TestGmp, ConvertStringToMpq) {
  auto [s, expected] = GetParam();
  expected.canonicalize();
  EXPECT_EQ(StringToMpq(s), expected);
}

TEST_P(TestGmp, ConvertStringToMpqPrefixPlus) {
  auto [s, expected] = GetParam();
  expected.canonicalize();
  EXPECT_EQ(StringToMpq("+" + s), expected);
}

TEST_P(TestGmp, ConvertStringToMpqPrefixMinus) {
  auto [s, expected] = GetParam();
  expected.canonicalize();
  EXPECT_EQ(StringToMpq("-" + s), -expected);
}