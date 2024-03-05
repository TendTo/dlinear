/**
 * @file TestTheorySolverBoundsVector.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include "dlinear/solver/TheorySolverBoundVector.h"

using dlinear::LpColBound;
using dlinear::TheorySolverBoundVector;

class TestSortedVector : public ::testing::Test {
 protected:
  std::vector<int> v_{1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
  TheorySolverBoundVector bounds_;

  TestSortedVector() {
    bounds_.AddBound(1, LpColBound::L, 6);
    bounds_.AddBound(2, LpColBound::L, 7);
    bounds_.AddBound(3, LpColBound::B, 8);
    bounds_.AddBound(4, LpColBound::U, 9);
    bounds_.AddBound(5, LpColBound::U, 10);
    DLINEAR_LOG_INIT_VERBOSITY(4);
  }
};

TEST_F(TestSortedVector, Constructor) {
  TheorySolverBoundVector bounds;
  EXPECT_EQ(bounds.n_upper_bounds(), 0);
  EXPECT_EQ(bounds.n_lower_bounds(), 0);
  EXPECT_EQ(bounds.bounds().size(), 0u);
}

TEST_F(TestSortedVector, AddLBound) {
  const mpq_class value{1};
  const int row_idx{0};
  TheorySolverBoundVector bounds;
  bounds.AddBound(value, LpColBound::L, row_idx);
  EXPECT_EQ(bounds.n_lower_bounds(), 1);
  EXPECT_EQ(bounds.n_upper_bounds(), 0);
  EXPECT_EQ(bounds.bounds().size(), 1u);
  const auto [b_value, b_row_idx] = bounds.bounds()[0];
  EXPECT_EQ(b_value, value);
  EXPECT_EQ(b_row_idx, row_idx);
}

TEST_F(TestSortedVector, AddUBound) {
  const mpq_class value{1};
  const int row_idx{0};
  TheorySolverBoundVector bounds;
  bounds.AddBound(value, LpColBound::U, row_idx);
  EXPECT_EQ(bounds.n_lower_bounds(), 0);
  EXPECT_EQ(bounds.n_upper_bounds(), 1);
  EXPECT_EQ(bounds.bounds().size(), 1u);
  const auto [b_value, b_row_idx] = bounds.bounds()[0];
  EXPECT_EQ(b_value, value);
  EXPECT_EQ(b_row_idx, row_idx);
}

TEST_F(TestSortedVector, AddBBound) {
  const mpq_class value{1};
  const int row_idx{0};
  TheorySolverBoundVector bounds;
  bounds.AddBound(value, LpColBound::B, row_idx);
  EXPECT_EQ(bounds.n_lower_bounds(), 1);
  EXPECT_EQ(bounds.n_upper_bounds(), 1);
  EXPECT_EQ(bounds.bounds().size(), 2u);
  const auto [b_value, b_row_idx] = bounds.bounds()[0];
  EXPECT_EQ(b_value, value);
  EXPECT_EQ(b_row_idx, row_idx);
  const auto [b_value2, b_row_idx2] = bounds.bounds()[1];
  EXPECT_EQ(b_value2, value);
  EXPECT_EQ(b_row_idx2, row_idx);
}

TEST_F(TestSortedVector, Clear) {
  bounds_.Clear();
  EXPECT_EQ(bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(bounds_.bounds().size(), 0u);
}

TEST_F(TestSortedVector, IsLowerBound) {
  std::cout << bounds_;
  EXPECT_TRUE(bounds_.IsLowerBound(1));
  EXPECT_TRUE(bounds_.IsLowerBound(2));
  EXPECT_TRUE(bounds_.IsLowerBound(3));
  EXPECT_FALSE(bounds_.IsLowerBound(4));
  EXPECT_FALSE(bounds_.IsLowerBound(5));
}

TEST_F(TestSortedVector, IsUpperBound) {
  EXPECT_FALSE(bounds_.IsUpperBound(1));
  EXPECT_FALSE(bounds_.IsUpperBound(2));
  EXPECT_TRUE(bounds_.IsUpperBound(3));
  EXPECT_TRUE(bounds_.IsUpperBound(4));
  EXPECT_TRUE(bounds_.IsUpperBound(5));
}

TEST_F(TestSortedVector, IsLowerSingle) {
  TheorySolverBoundVector bounds;
  bounds.AddBound(1, LpColBound::L, 0);
  EXPECT_TRUE(bounds.IsLowerBound(1));
  EXPECT_FALSE(bounds.IsUpperBound(1));
}

TEST_F(TestSortedVector, IsLowerBack) {
  TheorySolverBoundVector bounds;
  bounds.AddBound(1, LpColBound::L, 0);
  bounds.AddBound(2, LpColBound::L, 1);
  bounds.AddBound(3, LpColBound::L, 2);
  EXPECT_TRUE(bounds.IsLowerBound(3));
  EXPECT_FALSE(bounds.IsUpperBound(3));
}

TEST_F(TestSortedVector, IsUpperSingle) {
  TheorySolverBoundVector bounds;
  bounds.AddBound(1, LpColBound::U, 0);
  EXPECT_TRUE(bounds.IsUpperBound(1));
  EXPECT_FALSE(bounds.IsLowerBound(1));
}

TEST_F(TestSortedVector, IsUpperFront) {
  TheorySolverBoundVector bounds;
  bounds.AddBound(1, LpColBound::U, 0);
  bounds.AddBound(2, LpColBound::U, 1);
  bounds.AddBound(3, LpColBound::U, 2);
  EXPECT_TRUE(bounds.IsUpperBound(1));
  EXPECT_FALSE(bounds.IsLowerBound(1));
}

TEST_F(TestSortedVector, IsUpperIsLowerEqualityExplicit) {
  TheorySolverBoundVector bounds;
  bounds.AddBound(1, LpColBound::U, 0);
  bounds.AddBound(1, LpColBound::L, 0);
  EXPECT_TRUE(bounds.IsUpperBound(1));
  EXPECT_TRUE(bounds.IsLowerBound(1));
}

TEST_F(TestSortedVector, IsUpperIsLowerEqualityImplicit) {
  TheorySolverBoundVector bounds;
  bounds.AddBound(1, LpColBound::B, 0);
  EXPECT_TRUE(bounds.IsUpperBound(1));
  EXPECT_TRUE(bounds.IsLowerBound(1));
}

TEST_F(TestSortedVector, AddLowerOnEdge) {
  const auto violation = bounds_.AddBound(3, LpColBound::L, 0);
  EXPECT_FALSE(violation.has_value());
}
TEST_F(TestSortedVector, AddUpperOnEdge) {
  const auto violation = bounds_.AddBound(3, LpColBound::U, 0);
  EXPECT_FALSE(violation.has_value());
}
TEST_F(TestSortedVector, AddEqualOnEdge) {
  const auto violation = bounds_.AddBound(3, LpColBound::B, 0);
  EXPECT_FALSE(violation.has_value());
}

TEST_F(TestSortedVector, ViolationLowerOverUpperLeft) {
  const auto violation = bounds_.AddBound({35, 10}, LpColBound::L, 0);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation->second, bounds_.bounds().cend() - 2);
}
TEST_F(TestSortedVector, ViolationLowerOverUpperMiddle) {
  const auto violation = bounds_.AddBound({45, 10}, LpColBound::L, 0);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation->second, bounds_.bounds().cend() - 1);
}
TEST_F(TestSortedVector, ViolationLowerOverUpperRight) {
  const auto violation = bounds_.AddBound(6, LpColBound::L, 0);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation->second, bounds_.bounds().cend());
}

TEST_F(TestSortedVector, ViolationUpperOverLowerLeft) {
  const auto violation = bounds_.AddBound(0, LpColBound::U, 0);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin());
  EXPECT_EQ(violation->second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestSortedVector, ViolationUpperOverLowerMiddle) {
  const auto violation = bounds_.AddBound({15, 10}, LpColBound::U, 0);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation->second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestSortedVector, ViolationUpperOverLowerRight) {
  const auto violation = bounds_.AddBound({25, 10}, LpColBound::U, 0);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation->second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}

TEST_F(TestSortedVector, ViolationEqualOverLowerLeft) {
  const auto violation = bounds_.AddBound(0, LpColBound::B, 0);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin());
  EXPECT_EQ(violation->second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestSortedVector, ViolationEqualOverLowerMiddle) {
  const auto violation = bounds_.AddBound({15, 10}, LpColBound::B, 0);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation->second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestSortedVector, ViolationEqualOverLowerRight) {
  const auto violation = bounds_.AddBound({25, 10}, LpColBound::B, 0);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation->second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestSortedVector, ViolationEqualOverUpperLeft) {
  const auto violation = bounds_.AddBound({35, 10}, LpColBound::B, 0);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation->second, bounds_.bounds().cend() - 2);
}
TEST_F(TestSortedVector, ViolationEqualOverUpperMiddle) {
  const auto violation = bounds_.AddBound({45, 10}, LpColBound::B, 0);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation->second, bounds_.bounds().cend() - 1);
}
TEST_F(TestSortedVector, ViolationEqualOverUpperRight) {
  const auto violation = bounds_.AddBound(6, LpColBound::B, 0);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation->second, bounds_.bounds().cend());
}
