/**
 * @file TestSort.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include "dlinear/smt2/sort.h"

using dlinear::Variable;
using dlinear::smt2::ParseSort;
using dlinear::smt2::Sort;
using dlinear::smt2::SortToType;
using std::runtime_error;

TEST(TestSort, ParseSort) {
  EXPECT_EQ(ParseSort("Real"), Sort::Real);
  EXPECT_EQ(ParseSort("Int"), Sort::Int);
  EXPECT_EQ(ParseSort("Bool"), Sort::Bool);
  EXPECT_EQ(ParseSort("Binary"), Sort::Binary);
}

TEST(TestSort, ParseSortError) {
  EXPECT_THROW(ParseSort("real"), runtime_error);
  EXPECT_THROW(ParseSort("integer"), runtime_error);
  EXPECT_THROW(ParseSort("boolean"), runtime_error);
  EXPECT_THROW(ParseSort("binary"), runtime_error);
}

TEST(TestSort, SortToType) {
  EXPECT_EQ(SortToType(Sort::Real), Variable::Type::CONTINUOUS);
  EXPECT_EQ(SortToType(Sort::Int), Variable::Type::INTEGER);
  EXPECT_EQ(SortToType(Sort::Bool), Variable::Type::BOOLEAN);
  EXPECT_EQ(SortToType(Sort::Binary), Variable::Type::BINARY);
}
