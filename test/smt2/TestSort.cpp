/**
 * @file TestSort.cpp
 * @author dlinear
 * @date 21 Aug 2023
 * @copyright 2023 dlinear
 */

#include "dlinear/smt2/sort.h"

#include <gtest/gtest.h>

using dlinear::ParseSort;
using dlinear::Sort;
using std::runtime_error;
using dlinear::Variable;
using dlinear::SortToType;

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
