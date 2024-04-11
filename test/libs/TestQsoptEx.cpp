/**
 * @file TestQsoptEx.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#ifdef DLINEAR_ENABLED_QSOPT_EX
#include <gtest/gtest.h>

#include "dlinear/libs/libqsopt_ex.h"

using dlinear::qsopt_ex::MpqArray;
using dlinear::qsopt_ex::QSXFinish;
using dlinear::qsopt_ex::QSXStart;
using dlinear::qsopt_ex::StringToMpq;
using dlinear::qsopt_ex::StringToMpqPtr;

TEST(TestQsoptEx, QSXStartAndFinish) {
  EXPECT_NO_THROW(QSXStart());
  EXPECT_NO_THROW(QSXFinish());
}

TEST(TestQsoptEx, Array) {
  const uint n{10};
  mpq_class a{1};
  MpqArray array{n};
  mpq_t *ptr{array};
  mpq_set_d(array[0], a.get_d());

  EXPECT_TRUE(&array[0] == ptr);
  EXPECT_TRUE(mpq_equal(array[0], a.get_mpq_t()));
  EXPECT_EQ(array.size(), n);
}

TEST(TestQsoptEx, StringToMpqPtr) {
  EXPECT_EQ(*StringToMpqPtr("1"), mpq_class{1});
  EXPECT_EQ(*StringToMpqPtr("0"), mpq_class{0});
  EXPECT_EQ(*StringToMpqPtr("-1"), mpq_class{-1});
  EXPECT_EQ(*StringToMpqPtr("1/2"), mpq_class(1, 2u));
  EXPECT_EQ(*StringToMpqPtr("1/20"), mpq_class(1, 20));
}

TEST(TestQsoptEx, StringToMpq) {
  EXPECT_EQ(StringToMpq("1"), mpq_class{1});
  EXPECT_EQ(StringToMpq("0"), mpq_class{0});
  EXPECT_EQ(StringToMpq("-1"), mpq_class{-1});
  EXPECT_EQ(StringToMpq("1/2"), mpq_class(1, 2u));
  EXPECT_EQ(StringToMpq("1/20"), mpq_class(1, 20));
}
#endif