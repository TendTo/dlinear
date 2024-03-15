/**
 * @file TestTheorySolverBoundsVector.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include "dlinear/solver/TheorySolverBoundVector.h"

using dlinear::Literal;
using dlinear::LpColBound;
using dlinear::TheorySolverBoundVector;
using dlinear::Variable;

class TestTheorySolverBoundVector : public ::testing::Test {
 protected:
  const mpq_class inf_l_{-100};
  const mpq_class inf_u_{100};
  int idx_{0};
  TheorySolverBoundVector bounds_;
  TheorySolverBoundVector empty_bounds_;
  const mpq_class val_[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};

  TestTheorySolverBoundVector() : bounds_{inf_l_, inf_u_}, empty_bounds_{inf_l_, inf_u_} {
    bounds_.AddBound(val_[1], LpColBound::L, 6);
    bounds_.AddBound(val_[2], LpColBound::L, 7);
    bounds_.AddBound(val_[3], LpColBound::B, 8);
    bounds_.AddBound(val_[4], LpColBound::U, 9);
    bounds_.AddBound(val_[5], LpColBound::U, 10);
  }

  int idx() { return idx_++; }
};

TEST_F(TestTheorySolverBoundVector, Constructor) {
  TheorySolverBoundVector bounds{inf_l_, inf_u_};
  EXPECT_EQ(bounds.n_upper_bounds(), 0);
  EXPECT_EQ(bounds.n_lower_bounds(), 0);
  EXPECT_TRUE(bounds.bounds().empty());
  EXPECT_EQ(bounds.active_lower_bound(), inf_l_);
  EXPECT_EQ(bounds.active_upper_bound(), inf_u_);
  EXPECT_TRUE(bounds.nq_bounds().empty());
  EXPECT_EQ(bounds.inf_l(), inf_l_);
  EXPECT_EQ(bounds.inf_u(), inf_u_);
}

TEST_F(TestTheorySolverBoundVector, AddLBound) {
  const mpq_class value{1};
  const int bound_idx = 1;
  empty_bounds_.AddBound(value, LpColBound::L, bound_idx);
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 1);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(empty_bounds_.bounds().size(), 1u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), value);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
  const auto [b_value, b_type, b_bound_idx] = empty_bounds_.bounds()[0];
  EXPECT_EQ(*b_value, value);
  EXPECT_EQ(b_type, LpColBound::L);
  EXPECT_EQ(b_bound_idx, bound_idx);
  EXPECT_TRUE(empty_bounds_.nq_bounds().empty());
}

TEST_F(TestTheorySolverBoundVector, AddUBound) {
  const mpq_class value{1};
  const int bound_idx = 2;
  empty_bounds_.AddBound(value, LpColBound::U, bound_idx);
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 1);
  EXPECT_EQ(empty_bounds_.bounds().size(), 1u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), value);
  const auto [b_value, b_type, b_bound_idx] = empty_bounds_.bounds()[0];
  EXPECT_EQ(*b_value, value);
  EXPECT_EQ(b_type, LpColBound::U);
  EXPECT_EQ(b_bound_idx, bound_idx);
  EXPECT_TRUE(empty_bounds_.nq_bounds().empty());
}

TEST_F(TestTheorySolverBoundVector, AddBBound) {
  const mpq_class value{1};
  const int bound_idx = 3;
  empty_bounds_.AddBound(value, LpColBound::B, bound_idx);
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 1);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 1);
  EXPECT_EQ(empty_bounds_.bounds().size(), 2u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), value);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), value);
  const auto [b_value, b_type, b_bound_idx] = empty_bounds_.bounds()[0];
  EXPECT_EQ(*b_value, value);
  EXPECT_EQ(b_type, LpColBound::L);
  EXPECT_EQ(b_bound_idx, bound_idx);
  const auto [b_value2, b_type2, b_bound_idx2] = empty_bounds_.bounds()[1];
  EXPECT_EQ(*b_value2, value);
  EXPECT_EQ(b_type2, LpColBound::U);
  EXPECT_EQ(b_bound_idx2, bound_idx);
  EXPECT_TRUE(empty_bounds_.nq_bounds().empty());
}

TEST_F(TestTheorySolverBoundVector, AddSLBound) {
  const mpq_class value{1};
  const int bound_idx = 4;
  empty_bounds_.AddBound(value, LpColBound::SL, bound_idx);
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 1);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(empty_bounds_.bounds().size(), 1u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), value);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
  const auto [b_value, b_type, b_bound_idx] = empty_bounds_.bounds()[0];
  EXPECT_EQ(*b_value, value);
  EXPECT_EQ(b_type, LpColBound::SL);
  EXPECT_EQ(b_bound_idx, bound_idx);
  EXPECT_TRUE(empty_bounds_.nq_bounds().empty());
}

TEST_F(TestTheorySolverBoundVector, AddSUBound) {
  const mpq_class value{1};
  const int bound_idx = 5;
  empty_bounds_.AddBound(value, LpColBound::SU, bound_idx);
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 1);
  EXPECT_EQ(empty_bounds_.bounds().size(), 1u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), value);
  const auto [b_value, b_type, b_bound_idx] = empty_bounds_.bounds()[0];
  EXPECT_EQ(*b_value, value);
  EXPECT_EQ(b_type, LpColBound::SU);
  EXPECT_EQ(b_bound_idx, bound_idx);
  EXPECT_TRUE(empty_bounds_.nq_bounds().empty());
}

TEST_F(TestTheorySolverBoundVector, AddDBound) {
  const mpq_class value{1};
  const int bound_idx = 6;
  empty_bounds_.AddBound(value, LpColBound::D, bound_idx);
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(empty_bounds_.bounds().size(), 0u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
  EXPECT_EQ(empty_bounds_.nq_bounds().size(), 1u);
  EXPECT_EQ(*empty_bounds_.nq_bounds().begin(), std::make_tuple(&value, LpColBound::D, bound_idx));
}

TEST_F(TestTheorySolverBoundVector, NoNqActiveBounds) {
  auto it = bounds_.active_bounds();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() - 1);
  EXPECT_EQ(it.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() + 1);
}
TEST_F(TestTheorySolverBoundVector, OnlyLowerBoundsActiveBounds) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, idx());
  empty_bounds_.AddBound(val_[2], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::SL, idx());
  auto it = empty_bounds_.active_bounds();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cend() - 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestTheorySolverBoundVector, OnlyUpperBoundsActiveBounds) {
  empty_bounds_.AddBound(val_[1], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[1], LpColBound::SU, idx());
  empty_bounds_.AddBound(val_[2], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, idx());
  auto it = empty_bounds_.active_bounds();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cbegin() + 2);
}

TEST_F(TestTheorySolverBoundVector, NqBoundsActiveBounds) {
  empty_bounds_.AddBound(val_[0], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[0], LpColBound::SL, idx());
  empty_bounds_.AddBound(val_[0], LpColBound::D, idx());
  empty_bounds_.AddBound(val_[1], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, idx());
  empty_bounds_.AddBound(val_[1], LpColBound::D, idx());
  empty_bounds_.AddBound(val_[2], LpColBound::D, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::D, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, idx());
  empty_bounds_.AddBound(val_[4], LpColBound::D, idx());
  empty_bounds_.AddBound(val_[4], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[4], LpColBound::SU, idx());
  auto it = empty_bounds_.active_bounds();
  EXPECT_EQ(it.size(), 7u);
  EXPECT_EQ(it.nq_bounds_size(), 3u);
  EXPECT_EQ(it.bounds_size(), 4u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 2);
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin() + 1);
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend() - 1);
}

TEST_F(TestTheorySolverBoundVector, PriorityEqBoundsActiveBoundsOverLower) {
  const int eq_idx = idx();
  empty_bounds_.AddBound(val_[3], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::B, eq_idx);
  empty_bounds_.AddBound(val_[3], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::L, idx());
  auto it = empty_bounds_.active_bounds();
  std::cout << empty_bounds_ << std::endl;
  EXPECT_EQ(it.size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(*it.bounds().first, std::make_tuple(&val_[3], LpColBound::L, eq_idx));
  EXPECT_EQ(*(it.bounds().first + 1), std::make_tuple(&val_[3], LpColBound::U, eq_idx));
}
TEST_F(TestTheorySolverBoundVector, PriorityEqBoundsActiveBoundsOverUpper) {
  const int eq_idx = idx();
  empty_bounds_.AddBound(val_[3], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::B, eq_idx);
  empty_bounds_.AddBound(val_[3], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::U, idx());
  auto it = empty_bounds_.active_bounds();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(*it.bounds().first, std::make_tuple(&val_[3], LpColBound::L, eq_idx));
  EXPECT_EQ(*(it.bounds().first + 1), std::make_tuple(&val_[3], LpColBound::U, eq_idx));
}
TEST_F(TestTheorySolverBoundVector, EqBoundsActiveBounds) {
  empty_bounds_.AddBound(val_[3], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::B, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::U, idx());
  auto it = empty_bounds_.active_bounds();
  EXPECT_EQ(it.size(), 7u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 7u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
}

TEST_F(TestTheorySolverBoundVector, SetBounds) {
  mpq_class lb{1};
  mpq_class ub{2};
  empty_bounds_.SetBounds(lb, ub);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), lb);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), ub);
}
TEST_F(TestTheorySolverBoundVector, SetLowerBound) {
  mpq_class lb{1};
  empty_bounds_.SetLowerBound(lb);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), lb);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
}
TEST_F(TestTheorySolverBoundVector, SetUpperBound) {
  mpq_class ub{2};
  empty_bounds_.SetUpperBound(ub);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), ub);
}

TEST_F(TestTheorySolverBoundVector, SetBoundsUnchanged) {
  empty_bounds_.SetBounds(inf_l_ - 1, inf_u_ + 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
}
TEST_F(TestTheorySolverBoundVector, SetBoundsUnchangedLower) {
  mpq_class ub{2};
  empty_bounds_.SetBounds(inf_l_ - 1, ub);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), ub);
}
TEST_F(TestTheorySolverBoundVector, SetBoundsUnchangedUpper) {
  mpq_class lb{1};
  empty_bounds_.SetBounds(lb, inf_u_ + 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), lb);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
}
TEST_F(TestTheorySolverBoundVector, SetLowerBoundUnchanged) {
  empty_bounds_.SetLowerBound(inf_l_ - 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
}
TEST_F(TestTheorySolverBoundVector, SetUpperBoundUnchanged) {
  empty_bounds_.SetUpperBound(inf_u_ + 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
}

TEST_F(TestTheorySolverBoundVector, SetBoundsInvalid) {
  mpq_class lb{1};
  mpq_class ub{2};
  EXPECT_THROW(empty_bounds_.SetBounds(ub, lb), std::runtime_error);
}
TEST_F(TestTheorySolverBoundVector, SetLowerBoundInvalid) {
  EXPECT_THROW(empty_bounds_.SetLowerBound(inf_u_ + 1), std::runtime_error);
}
TEST_F(TestTheorySolverBoundVector, SetUpperBoundInvalid) {
  EXPECT_THROW(empty_bounds_.SetUpperBound(inf_l_ - 1), std::runtime_error);
}

TEST_F(TestTheorySolverBoundVector, Clear) {
  bounds_.Clear();
  EXPECT_EQ(bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(bounds_.bounds().size(), 0u);
  EXPECT_EQ(bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(bounds_.active_upper_bound(), inf_u_);
  EXPECT_EQ(bounds_.inf_l(), inf_l_);
  EXPECT_EQ(bounds_.inf_u(), inf_u_);
}

TEST_F(TestTheorySolverBoundVector, IsActiveEquality) { EXPECT_TRUE(bounds_.IsActiveEquality(3)); }

TEST_F(TestTheorySolverBoundVector, IsActiveEqualityLUBounds) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[1], LpColBound::U, idx());
  EXPECT_TRUE(empty_bounds_.IsActiveEquality(1));
}

TEST_F(TestTheorySolverBoundVector, IsLowerBound) {
  EXPECT_TRUE(bounds_.IsLowerBound(1));
  EXPECT_TRUE(bounds_.IsLowerBound(2));
  EXPECT_TRUE(bounds_.IsLowerBound(3));
  EXPECT_FALSE(bounds_.IsLowerBound(4));
  EXPECT_FALSE(bounds_.IsLowerBound(5));
}

TEST_F(TestTheorySolverBoundVector, IsUpperBound) {
  EXPECT_FALSE(bounds_.IsUpperBound(1));
  EXPECT_FALSE(bounds_.IsUpperBound(2));
  EXPECT_TRUE(bounds_.IsUpperBound(3));
  EXPECT_TRUE(bounds_.IsUpperBound(4));
  EXPECT_TRUE(bounds_.IsUpperBound(5));
}

TEST_F(TestTheorySolverBoundVector, IsLowerSingle) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, idx());
  EXPECT_TRUE(empty_bounds_.IsLowerBound(1));
  EXPECT_FALSE(empty_bounds_.IsUpperBound(1));
}

TEST_F(TestTheorySolverBoundVector, IsLowerBack) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[2], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::L, idx());
  EXPECT_TRUE(empty_bounds_.IsLowerBound(3));
  EXPECT_FALSE(empty_bounds_.IsUpperBound(3));
}

TEST_F(TestTheorySolverBoundVector, IsUpperSingle) {
  empty_bounds_.AddBound(val_[1], LpColBound::U, idx());
  EXPECT_TRUE(empty_bounds_.IsUpperBound(1));
  EXPECT_FALSE(empty_bounds_.IsLowerBound(1));
}

TEST_F(TestTheorySolverBoundVector, IsUpperFront) {
  empty_bounds_.AddBound(val_[1], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[2], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::U, idx());
  EXPECT_TRUE(empty_bounds_.IsUpperBound(1));
  EXPECT_FALSE(empty_bounds_.IsLowerBound(1));
}

TEST_F(TestTheorySolverBoundVector, IsUpperIsLowerEqualityExplicit) {
  empty_bounds_.AddBound(val_[1], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[1], LpColBound::L, idx());
  EXPECT_TRUE(empty_bounds_.IsUpperBound(1));
  EXPECT_TRUE(empty_bounds_.IsLowerBound(1));
}

TEST_F(TestTheorySolverBoundVector, IsUpperIsLowerEqualityImplicit) {
  empty_bounds_.AddBound(val_[1], LpColBound::B, idx());
  EXPECT_TRUE(empty_bounds_.IsUpperBound(1));
  EXPECT_TRUE(empty_bounds_.IsLowerBound(1));
}

TEST_F(TestTheorySolverBoundVector, AddLowerOnEdge) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::L, idx());
  EXPECT_FALSE(violation);
}
TEST_F(TestTheorySolverBoundVector, AddUpperOnEdge) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::U, idx());
  EXPECT_FALSE(violation);
}
TEST_F(TestTheorySolverBoundVector, AddEqualOnEdge) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::B, idx());
  EXPECT_FALSE(violation);
}

TEST_F(TestTheorySolverBoundVector, ViolationLowerOverUpperLeft) {
  const auto violation = bounds_.AddBound({35, 10}, LpColBound::L, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend() - 2);
}
TEST_F(TestTheorySolverBoundVector, ViolationLowerOverUpperMiddle) {
  const auto violation = bounds_.AddBound({45, 10}, LpColBound::L, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend() - 1);
}
TEST_F(TestTheorySolverBoundVector, ViolationLowerOverUpperRight) {
  const auto violation = bounds_.AddBound(val_[6], LpColBound::L, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend());
}

TEST_F(TestTheorySolverBoundVector, ViolationUpperOverLowerLeft) {
  const auto violation = bounds_.AddBound(val_[0], LpColBound::U, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestTheorySolverBoundVector, ViolationUpperOverLowerMiddle) {
  const auto violation = bounds_.AddBound({15, 10}, LpColBound::U, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestTheorySolverBoundVector, ViolationUpperOverLowerRight) {
  const auto violation = bounds_.AddBound({25, 10}, LpColBound::U, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}

TEST_F(TestTheorySolverBoundVector, ViolationEqualOverLowerLeft) {
  const auto violation = bounds_.AddBound(val_[0], LpColBound::B, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestTheorySolverBoundVector, ViolationEqualOverLowerMiddle) {
  const auto violation = bounds_.AddBound({15, 10}, LpColBound::B, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestTheorySolverBoundVector, ViolationEqualOverLowerRight) {
  const auto violation = bounds_.AddBound({25, 10}, LpColBound::B, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestTheorySolverBoundVector, ViolationEqualOverUpperLeft) {
  const auto violation = bounds_.AddBound({35, 10}, LpColBound::B, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend() - 2);
}
TEST_F(TestTheorySolverBoundVector, ViolationEqualOverUpperMiddle) {
  const auto violation = bounds_.AddBound({45, 10}, LpColBound::B, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend() - 1);
}
TEST_F(TestTheorySolverBoundVector, ViolationEqualOverUpperRight) {
  const auto violation = bounds_.AddBound(val_[6], LpColBound::B, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend());
}
TEST_F(TestTheorySolverBoundVector, ViolationEqualOverMultipleLower) {
  empty_bounds_.AddBound(val_[0], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[1], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, idx());
  empty_bounds_.AddBound(val_[2], LpColBound::L, idx());
  const auto violation = empty_bounds_.AddBound(val_[1], LpColBound::B, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestTheorySolverBoundVector, ViolationEqualOverMultipleUpper) {
  empty_bounds_.AddBound(val_[0], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[1], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[1], LpColBound::SU, idx());
  empty_bounds_.AddBound(val_[2], LpColBound::U, idx());
  const auto violation = empty_bounds_.AddBound(val_[1], LpColBound::B, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cbegin() + 2);
}

TEST_F(TestTheorySolverBoundVector, ViolationStrictLowerOverEquality) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::SL, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() + 1);
}
TEST_F(TestTheorySolverBoundVector, ViolationStrictUpperOverEquality) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::SU, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() - 1);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestTheorySolverBoundVector, ViolationStrictInequalityOverEquality) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::D, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() - 1);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() + 1);
}

TEST_F(TestTheorySolverBoundVector, ViolationLowerOverStrictInequality) {
  empty_bounds_.AddBound(val_[2], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::U, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::D, idx());
  empty_bounds_.AddBound(val_[4], LpColBound::U, idx());
  const auto violation = empty_bounds_.AddBound(val_[3], LpColBound::L, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 1u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 1);
  EXPECT_EQ(violation.nq_bounds_size(), 1u);
  EXPECT_EQ(violation.nq_bounds().first, empty_bounds_.nq_bounds().cbegin());
  EXPECT_EQ(violation.nq_bounds().second, empty_bounds_.nq_bounds().cend());
}

TEST_F(TestTheorySolverBoundVector, ViolationUpperOverStrictInequality) {
  empty_bounds_.AddBound(val_[2], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::L, idx());
  empty_bounds_.AddBound(val_[3], LpColBound::D, idx());
  empty_bounds_.AddBound(val_[4], LpColBound::U, idx());
  const auto violation = empty_bounds_.AddBound(val_[3], LpColBound::U, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 1u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 1);
  EXPECT_EQ(violation.nq_bounds_size(), 1u);
  EXPECT_EQ(violation.nq_bounds().first, empty_bounds_.nq_bounds().cbegin());
  EXPECT_EQ(violation.nq_bounds().second, empty_bounds_.nq_bounds().cend());
}

TEST_F(TestTheorySolverBoundVector, ViolationUpperOverStrictLower) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, idx()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::U, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cbegin() + 1);
}

TEST_F(TestTheorySolverBoundVector, ViolationLowerOverStrictUpper) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SU, idx()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::L, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cbegin() + 1);
}

TEST_F(TestTheorySolverBoundVector, ViolationUpperOverStrictLowerStandardViolationAdditionalElement) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SL, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::L, idx()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::U, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 4u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestTheorySolverBoundVector, ViolationLowerOverStrictUpperStandardViolationAdditionalElement) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SU, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::U, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, idx()));
  auto violation = empty_bounds_.AddBound(val_[2], LpColBound::L, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 4u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 2);
}

TEST_F(TestTheorySolverBoundVector, ViolationUpperOverStrictLowerStandardViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, idx()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::U, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestTheorySolverBoundVector, ViolationLowerOverStrictUpperStandardViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, idx()));
  auto violation = empty_bounds_.AddBound(val_[2], LpColBound::L, idx());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 2);
}

TEST_F(TestTheorySolverBoundVector, ViolationUpperOverStrictLowerStandardNoViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SL, idx()));
  auto violation = empty_bounds_.AddBound(val_[3], LpColBound::U, idx());
  EXPECT_FALSE(violation);
}

TEST_F(TestTheorySolverBoundVector, ViolationLowerOverStrictUpperStandardNoViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SU, idx()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, idx()));
  auto violation = empty_bounds_.AddBound(val_[0], LpColBound::L, idx());
  EXPECT_FALSE(violation);
}
