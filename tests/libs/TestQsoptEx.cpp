/**
 * @file TestQsoptEx.cpp
 * @author dlinear
 * @date 19 Aug 2023
 * @copyright 2023 dlinear
 */
#include "dlinear/libs/qsopt_ex.h"

#include <gtest/gtest.h>

using dlinear::qsopt_ex::StringToMpqPtr;
using dlinear::qsopt_ex::StringToMpq;
using dlinear::qsopt_ex::MpqArray;
using dlinear::qsopt_ex::QSXStart;
using dlinear::qsopt_ex::QSXFinish;

TEST(TestQsoptEx, QSXStartAndFinish) {
  EXPECT_NO_THROW(QSXStart());
  EXPECT_NO_THROW(QSXFinish());
}

TEST(TestQsoptEx, TestArray) {
  const uint n{10};
  mpq_class a{1};
  MpqArray array{n};
  mpq_t *ptr{array};
  mpq_set_d(array[0], a.get_d());

  EXPECT_TRUE(&array[0] == ptr);
  EXPECT_TRUE(mpq_equal(array[0], a.get_mpq_t()));
  EXPECT_EQ(array.size(), n);
}

TEST(TestQsoptEx, TestStringToMpqPtr) {
  EXPECT_EQ(*StringToMpqPtr("1"), mpq_class{1});
  EXPECT_EQ(*StringToMpqPtr("0"), mpq_class{0});
  EXPECT_EQ(*StringToMpqPtr("-1"), mpq_class{-1});
  EXPECT_EQ(*StringToMpqPtr("1/2"), mpq_class(1, 2u));
  EXPECT_EQ(*StringToMpqPtr("1/20"), mpq_class(1, 20));
}

TEST(TestQsoptEx, TestStringToMpq) {
  EXPECT_EQ(StringToMpq("1"), mpq_class{1});
  EXPECT_EQ(StringToMpq("0"), mpq_class{0});
  EXPECT_EQ(StringToMpq("-1"), mpq_class{-1});
  EXPECT_EQ(StringToMpq("1/2"), mpq_class(1, 2u));
  EXPECT_EQ(StringToMpq("1/20"), mpq_class(1, 20));
}
