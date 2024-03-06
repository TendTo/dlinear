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

class TestSortedVector : public ::testing::Test {
 protected:
  const mpq_class inf_{100};
  const mpq_class inf_l_{-100};
  const mpq_class inf_u_{100};
  const Literal lit_{Variable{"x"}, true};
  TheorySolverBoundVector bounds_;
  TheorySolverBoundVector empty_bounds_;

  TestSortedVector() : bounds_{inf_}, empty_bounds_{inf_} {
    bounds_.AddBound(1, LpColBound::L, {Variable{"a"}, true});
    bounds_.AddBound(2, LpColBound::L, {Variable{"b"}, true});
    bounds_.AddBound(3, LpColBound::B, {Variable{"c"}, true});
    bounds_.AddBound(4, LpColBound::U, {Variable{"d"}, true});
    bounds_.AddBound(5, LpColBound::U, {Variable{"e"}, true});
    DLINEAR_LOG_INIT_VERBOSITY(2);
  }
};

TEST_F(TestSortedVector, ConstructorSingle) {
  TheorySolverBoundVector bounds{inf_};
  EXPECT_EQ(bounds.n_upper_bounds(), 0);
  EXPECT_EQ(bounds.n_lower_bounds(), 0);
  EXPECT_EQ(bounds.bounds().size(), 0u);
  EXPECT_EQ(bounds.active_lower_bound(), -inf_);
  EXPECT_EQ(bounds.active_upper_bound(), inf_);
  EXPECT_EQ(bounds.nq_values().size(), 0u);
  EXPECT_EQ(bounds.inf_l(), -inf_);
  EXPECT_EQ(bounds.inf_u(), inf_);
}

TEST_F(TestSortedVector, ConstructorDouble) {
  TheorySolverBoundVector bounds{inf_l_, inf_u_};
  EXPECT_EQ(bounds.n_upper_bounds(), 0);
  EXPECT_EQ(bounds.n_lower_bounds(), 0);
  EXPECT_EQ(bounds.bounds().size(), 0u);
  EXPECT_EQ(bounds.active_lower_bound(), inf_l_);
  EXPECT_EQ(bounds.active_upper_bound(), inf_u_);
  EXPECT_EQ(bounds.nq_values().size(), 0u);
  EXPECT_EQ(bounds.inf_l(), inf_l_);
  EXPECT_EQ(bounds.inf_u(), inf_u_);
}

TEST_F(TestSortedVector, AddLBound) {
  const mpq_class value{1};
  const Literal row_lit{Variable{"x"}, true};
  TheorySolverBoundVector bounds{inf_};
  bounds.AddBound(value, LpColBound::L, row_lit);
  EXPECT_EQ(bounds.n_lower_bounds(), 1);
  EXPECT_EQ(bounds.n_upper_bounds(), 0);
  EXPECT_EQ(bounds.bounds().size(), 1u);
  EXPECT_EQ(bounds.active_lower_bound(), value);
  EXPECT_EQ(bounds.active_upper_bound(), 100);
  EXPECT_EQ(bounds.active_lower_bound(), value);
  EXPECT_EQ(bounds.active_upper_bound(), inf_);
  const auto [b_value, b_row_lit] = bounds.bounds()[0];
  EXPECT_EQ(b_value, value);
  EXPECT_TRUE(std::equal_to<Literal>{}(b_row_lit, row_lit));
  EXPECT_EQ(bounds.nq_values().size(), 0u);
}

TEST_F(TestSortedVector, AddUBound) {
  const mpq_class value{1};
  const Literal row_lit{Variable{"y"}, true};
  TheorySolverBoundVector bounds{inf_};
  bounds.AddBound(value, LpColBound::U, row_lit);
  EXPECT_EQ(bounds.n_lower_bounds(), 0);
  EXPECT_EQ(bounds.n_upper_bounds(), 1);
  EXPECT_EQ(bounds.bounds().size(), 1u);
  EXPECT_EQ(bounds.active_lower_bound(), -inf_);
  EXPECT_EQ(bounds.active_upper_bound(), value);
  const auto [b_value, b_row_lit] = bounds.bounds()[0];
  EXPECT_EQ(b_value, value);
  EXPECT_TRUE(std::equal_to<Literal>{}(b_row_lit, row_lit));
  EXPECT_EQ(bounds.nq_values().size(), 0u);
}

TEST_F(TestSortedVector, AddBBound) {
  const mpq_class value{1};
  const Literal row_lit{Variable{"z"}, true};
  TheorySolverBoundVector bounds{inf_};
  bounds.AddBound(value, LpColBound::B, row_lit);
  EXPECT_EQ(bounds.n_lower_bounds(), 1);
  EXPECT_EQ(bounds.n_upper_bounds(), 1);
  EXPECT_EQ(bounds.bounds().size(), 2u);
  EXPECT_EQ(bounds.active_lower_bound(), value);
  EXPECT_EQ(bounds.active_upper_bound(), value);
  const auto [b_value, b_row_lit] = bounds.bounds()[0];
  EXPECT_EQ(b_value, value);
  EXPECT_TRUE(std::equal_to<Literal>{}(b_row_lit, row_lit));
  const auto [b_value2, b_row_lit2] = bounds.bounds()[1];
  EXPECT_EQ(b_value2, value);
  EXPECT_TRUE(std::equal_to<Literal>{}(b_row_lit2, row_lit));
  EXPECT_EQ(bounds.nq_values().size(), 0u);
}

TEST_F(TestSortedVector, AddSLBound) {
  const mpq_class value{1};
  const Literal row_lit{Variable{"t"}, true};
  TheorySolverBoundVector bounds{inf_};
  bounds.AddBound(value, LpColBound::SL, row_lit);
  EXPECT_EQ(bounds.n_lower_bounds(), 1);
  EXPECT_EQ(bounds.n_upper_bounds(), 0);
  EXPECT_EQ(bounds.bounds().size(), 1u);
  EXPECT_EQ(bounds.active_lower_bound(), value);
  EXPECT_EQ(bounds.active_upper_bound(), inf_);
  const auto [b_value, b_row_lit] = bounds.bounds()[0];
  EXPECT_EQ(b_value, value);
  EXPECT_TRUE(std::equal_to<Literal>{}(b_row_lit, row_lit));
  EXPECT_EQ(bounds.nq_values().size(), 1u);
  EXPECT_EQ(*bounds.nq_values().begin(), value);
}

TEST_F(TestSortedVector, AddSUBound) {
  const mpq_class value{1};
  const Literal row_lit{Variable{"z"}, true};
  TheorySolverBoundVector bounds{inf_};
  bounds.AddBound(value, LpColBound::SU, row_lit);
  EXPECT_EQ(bounds.n_lower_bounds(), 0);
  EXPECT_EQ(bounds.n_upper_bounds(), 1);
  EXPECT_EQ(bounds.bounds().size(), 1u);
  EXPECT_EQ(bounds.active_lower_bound(), -inf_);
  EXPECT_EQ(bounds.active_upper_bound(), value);
  const auto [b_value, b_row_lit] = bounds.bounds()[0];
  EXPECT_EQ(b_value, value);
  EXPECT_TRUE(std::equal_to<Literal>{}(b_row_lit, row_lit));
  EXPECT_EQ(bounds.nq_values().size(), 1u);
  EXPECT_EQ(*bounds.nq_values().begin(), value);
}

TEST_F(TestSortedVector, AddDBound) {
  const mpq_class value{1};
  const Literal row_lit{Variable{"d"}, true};
  TheorySolverBoundVector bounds{inf_};
  bounds.AddBound(value, LpColBound::D, row_lit);
  EXPECT_EQ(bounds.n_lower_bounds(), 0);
  EXPECT_EQ(bounds.n_upper_bounds(), 0);
  EXPECT_EQ(bounds.bounds().size(), 0u);
  EXPECT_EQ(bounds.active_lower_bound(), -inf_);
  EXPECT_EQ(bounds.active_upper_bound(), inf_);
  EXPECT_EQ(bounds.nq_values().size(), 1u);
  EXPECT_EQ(*bounds.nq_values().begin(), value);
}

TEST_F(TestSortedVector, SetBounds) {
  mpq_class lb{1};
  mpq_class ub{2};
  empty_bounds_.SetBounds(lb, ub);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), lb);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), ub);
}
TEST_F(TestSortedVector, SetLowerBound) {
  mpq_class lb{1};
  empty_bounds_.SetLowerBound(lb);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), lb);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_);
}
TEST_F(TestSortedVector, SetUpperBound) {
  mpq_class ub{2};
  empty_bounds_.SetUpperBound(ub);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), -inf_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), ub);
}

TEST_F(TestSortedVector, SetBoundsUnchanged) {
  empty_bounds_.SetBounds(-inf_ - 1, inf_ + 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), -inf_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_);
}
TEST_F(TestSortedVector, SetBoundsUnchangedLower) {
  mpq_class ub{2};
  empty_bounds_.SetBounds(-inf_ - 1, ub);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), -inf_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), ub);
}
TEST_F(TestSortedVector, SetBoundsUnchangedUpper) {
  mpq_class lb{1};
  empty_bounds_.SetBounds(lb, inf_ + 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), lb);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_);
}
TEST_F(TestSortedVector, SetLowerBoundUnchanged) {
  empty_bounds_.SetLowerBound(-inf_ - 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), -inf_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_);
}
TEST_F(TestSortedVector, SetUpperBoundUnchanged) {
  empty_bounds_.SetUpperBound(inf_ + 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), -inf_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_);
}

TEST_F(TestSortedVector, SetBoundsInvalid) {
  mpq_class lb{1};
  mpq_class ub{2};
  EXPECT_THROW(empty_bounds_.SetBounds(ub, lb), std::runtime_error);
}
TEST_F(TestSortedVector, SetLowerBoundInvalid) {
  EXPECT_THROW(empty_bounds_.SetLowerBound(inf_ + 1), std::runtime_error);
}
TEST_F(TestSortedVector, SetUpperBoundInvalid) {
  EXPECT_THROW(empty_bounds_.SetUpperBound(-inf_ - 1), std::runtime_error);
}

TEST_F(TestSortedVector, Clear) {
  bounds_.Clear();
  EXPECT_EQ(bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(bounds_.bounds().size(), 0u);
  EXPECT_EQ(bounds_.active_lower_bound(), -inf_);
  EXPECT_EQ(bounds_.active_upper_bound(), inf_);
  EXPECT_EQ(bounds_.inf_l(), -inf_);
  EXPECT_EQ(bounds_.inf_u(), inf_);
}

TEST_F(TestSortedVector, ClearSingle) {
  const mpq_class inf{1};
  bounds_.Clear(inf);
  EXPECT_EQ(bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(bounds_.bounds().size(), 0u);
  EXPECT_EQ(bounds_.active_lower_bound(), -inf);
  EXPECT_EQ(bounds_.active_upper_bound(), inf);
  EXPECT_EQ(bounds_.inf_l(), -inf);
  EXPECT_EQ(bounds_.inf_u(), inf);
}

TEST_F(TestSortedVector, ClearDouble) {
  const mpq_class inf_l{1};
  const mpq_class inf_u{2};
  bounds_.Clear(inf_l, inf_u);
  EXPECT_EQ(bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(bounds_.bounds().size(), 0u);
  EXPECT_EQ(bounds_.active_lower_bound(), inf_l);
  EXPECT_EQ(bounds_.active_upper_bound(), inf_u);
  EXPECT_EQ(bounds_.inf_l(), inf_l);
  EXPECT_EQ(bounds_.inf_u(), inf_u);
}

TEST_F(TestSortedVector, IsActiveEquality) { EXPECT_TRUE(bounds_.IsActiveEquality(3)); }

TEST_F(TestSortedVector, IsActiveEqualityLUBounds) {
  TheorySolverBoundVector bounds{inf_};
  bounds.AddBound(1, LpColBound::L, lit_);
  bounds.AddBound(1, LpColBound::U, lit_);
  EXPECT_TRUE(bounds.IsActiveEquality(1));
}

TEST_F(TestSortedVector, IsLowerBound) {
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
  TheorySolverBoundVector bounds{-100, 100};
  bounds.AddBound(1, LpColBound::L, lit_);
  EXPECT_TRUE(bounds.IsLowerBound(1));
  EXPECT_FALSE(bounds.IsUpperBound(1));
}

TEST_F(TestSortedVector, IsLowerBack) {
  TheorySolverBoundVector bounds{-100, 100};
  bounds.AddBound(1, LpColBound::L, lit_);
  bounds.AddBound(2, LpColBound::L, lit_);
  bounds.AddBound(3, LpColBound::L, lit_);
  EXPECT_TRUE(bounds.IsLowerBound(3));
  EXPECT_FALSE(bounds.IsUpperBound(3));
}

TEST_F(TestSortedVector, IsUpperSingle) {
  TheorySolverBoundVector bounds{-100, 100};
  bounds.AddBound(1, LpColBound::U, lit_);
  EXPECT_TRUE(bounds.IsUpperBound(1));
  EXPECT_FALSE(bounds.IsLowerBound(1));
}

TEST_F(TestSortedVector, IsUpperFront) {
  TheorySolverBoundVector bounds{-100, 100};
  bounds.AddBound(1, LpColBound::U, lit_);
  bounds.AddBound(2, LpColBound::U, lit_);
  bounds.AddBound(3, LpColBound::U, lit_);
  EXPECT_TRUE(bounds.IsUpperBound(1));
  EXPECT_FALSE(bounds.IsLowerBound(1));
}

TEST_F(TestSortedVector, IsUpperIsLowerEqualityExplicit) {
  TheorySolverBoundVector bounds{-100, 100};
  bounds.AddBound(1, LpColBound::U, lit_);
  bounds.AddBound(1, LpColBound::L, lit_);
  EXPECT_TRUE(bounds.IsUpperBound(1));
  EXPECT_TRUE(bounds.IsLowerBound(1));
}

TEST_F(TestSortedVector, IsUpperIsLowerEqualityImplicit) {
  TheorySolverBoundVector bounds{-100, 100};
  bounds.AddBound(1, LpColBound::B, lit_);
  EXPECT_TRUE(bounds.IsUpperBound(1));
  EXPECT_TRUE(bounds.IsLowerBound(1));
}

TEST_F(TestSortedVector, AddLowerOnEdge) {
  const auto violation = bounds_.AddBound(3, LpColBound::L, lit_);
  EXPECT_FALSE(violation.has_value());
}
TEST_F(TestSortedVector, AddUpperOnEdge) {
  const auto violation = bounds_.AddBound(3, LpColBound::U, lit_);
  EXPECT_FALSE(violation.has_value());
}
TEST_F(TestSortedVector, AddEqualOnEdge) {
  const auto violation = bounds_.AddBound(3, LpColBound::B, lit_);
  EXPECT_FALSE(violation.has_value());
}

TEST_F(TestSortedVector, ViolationLowerOverUpperLeft) {
  const auto violation = bounds_.AddBound({35, 10}, LpColBound::L, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation->second, bounds_.bounds().cend() - 2);
}
TEST_F(TestSortedVector, ViolationLowerOverUpperMiddle) {
  const auto violation = bounds_.AddBound({45, 10}, LpColBound::L, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation->second, bounds_.bounds().cend() - 1);
}
TEST_F(TestSortedVector, ViolationLowerOverUpperRight) {
  const auto violation = bounds_.AddBound(6, LpColBound::L, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation->second, bounds_.bounds().cend());
}

TEST_F(TestSortedVector, ViolationUpperOverLowerLeft) {
  const auto violation = bounds_.AddBound(0, LpColBound::U, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin());
  EXPECT_EQ(violation->second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestSortedVector, ViolationUpperOverLowerMiddle) {
  const auto violation = bounds_.AddBound({15, 10}, LpColBound::U, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation->second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestSortedVector, ViolationUpperOverLowerRight) {
  const auto violation = bounds_.AddBound({25, 10}, LpColBound::U, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation->second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}

TEST_F(TestSortedVector, ViolationEqualOverLowerLeft) {
  const auto violation = bounds_.AddBound(0, LpColBound::B, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin());
  EXPECT_EQ(violation->second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestSortedVector, ViolationEqualOverLowerMiddle) {
  const auto violation = bounds_.AddBound({15, 10}, LpColBound::B, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation->second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestSortedVector, ViolationEqualOverLowerRight) {
  const auto violation = bounds_.AddBound({25, 10}, LpColBound::B, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation->second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestSortedVector, ViolationEqualOverUpperLeft) {
  const auto violation = bounds_.AddBound({35, 10}, LpColBound::B, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation->second, bounds_.bounds().cend() - 2);
}
TEST_F(TestSortedVector, ViolationEqualOverUpperMiddle) {
  const auto violation = bounds_.AddBound({45, 10}, LpColBound::B, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation->second, bounds_.bounds().cend() - 1);
}
TEST_F(TestSortedVector, ViolationEqualOverUpperRight) {
  const auto violation = bounds_.AddBound(6, LpColBound::B, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation->second, bounds_.bounds().cend());
}

TEST_F(TestSortedVector, ViolationStrictLowerOverEquality) {
  const auto violation = bounds_.AddBound(3, LpColBound::SL, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() - 1);
  EXPECT_EQ(violation->second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() + 1);
}
TEST_F(TestSortedVector, ViolationStrictUpperOverEquality) {
  const auto violation = bounds_.AddBound(3, LpColBound::SU, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() - 1);
  EXPECT_EQ(violation->second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() + 1);
}
TEST_F(TestSortedVector, ViolationStrictInequalityOverEquality) {
  const auto violation = bounds_.AddBound(3, LpColBound::D, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() - 1);
  EXPECT_EQ(violation->second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() + 1);
}

TEST_F(TestSortedVector, ViolationUpperOverStrictLower) {
  EXPECT_FALSE(empty_bounds_.AddBound(1, LpColBound::SL, lit_));
  auto violation = empty_bounds_.AddBound(1, LpColBound::U, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation->second, empty_bounds_.bounds().cbegin() + 1);
}

TEST_F(TestSortedVector, ViolationLowerOverStrictUpper) {
  EXPECT_FALSE(empty_bounds_.AddBound(1, LpColBound::SU, lit_));
  auto violation = empty_bounds_.AddBound(1, LpColBound::L, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation->second, empty_bounds_.bounds().cbegin() + 1);
}

TEST_F(TestSortedVector, ViolationUpperOverStrictLowerStandardViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(1, LpColBound::SL, lit_));
  EXPECT_FALSE(empty_bounds_.AddBound(2, LpColBound::SL, lit_));
  auto violation = empty_bounds_.AddBound(1, LpColBound::U, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation->second, empty_bounds_.bounds().cend());
}

TEST_F(TestSortedVector, ViolationLowerOverStrictUpperStandardViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(1, LpColBound::SU, lit_));
  EXPECT_FALSE(empty_bounds_.AddBound(2, LpColBound::SU, lit_));
  auto violation = empty_bounds_.AddBound(2, LpColBound::L, lit_);
  EXPECT_TRUE(violation.has_value());
  EXPECT_EQ(violation->first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation->second, empty_bounds_.bounds().cbegin() + 1);
}

TEST_F(TestSortedVector, ViolationUpperOverStrictLowerStandardNoViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(1, LpColBound::SL, lit_));
  EXPECT_FALSE(empty_bounds_.AddBound(2, LpColBound::SL, lit_));
  auto violation = empty_bounds_.AddBound(3, LpColBound::U, lit_);
  EXPECT_FALSE(violation.has_value());
}

TEST_F(TestSortedVector, ViolationLowerOverStrictUpperStandardNoViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(1, LpColBound::SU, lit_));
  EXPECT_FALSE(empty_bounds_.AddBound(2, LpColBound::SU, lit_));
  auto violation = empty_bounds_.AddBound(0, LpColBound::L, lit_);
  EXPECT_FALSE(violation.has_value());
}
