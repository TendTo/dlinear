/**
 * @file TestTheorySolverBoundsVector.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include "dlinear/solver/BoundVector.h"

using dlinear::BoundVector;
using dlinear::Literal;
using dlinear::LpColBound;
using dlinear::Variable;
using dlinear::Bound;

class TestContextBoundVector : public ::testing::Test {
 protected:
  const mpq_class inf_l_{-100};
  const mpq_class inf_u_{100};
  int idx_{0};
  BoundVector bounds_;
  BoundVector empty_bounds_;
  const mpq_class val_[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
  Literal exp1_, exp2_, exp3_, exp4_, exp5_;

  TestContextBoundVector() : bounds_{inf_l_, inf_u_}, empty_bounds_{inf_l_, inf_u_} {
    bounds_.AddBound(val_[1], LpColBound::L, {exp1_});
    bounds_.AddBound(val_[2], LpColBound::L, {exp2_});
    bounds_.AddBound(val_[3], LpColBound::B, {exp3_});
    bounds_.AddBound(val_[4], LpColBound::U, {exp4_});
    bounds_.AddBound(val_[5], LpColBound::U, {exp5_});
  }

  std::set<Literal> exp() {
    return {Literal{Variable{"exp" + std::to_string(idx_++), Variable::Type::BOOLEAN}, static_cast<bool>(idx_ & 1)}};
  }
};

TEST_F(TestContextBoundVector, Constructor) {
  BoundVector bounds{inf_l_, inf_u_};
  EXPECT_EQ(bounds.n_upper_bounds(), 0);
  EXPECT_EQ(bounds.n_lower_bounds(), 0);
  EXPECT_TRUE(bounds.bounds().empty());
  EXPECT_EQ(bounds.active_lower_bound(), inf_l_);
  EXPECT_EQ(bounds.active_upper_bound(), inf_u_);
  EXPECT_TRUE(bounds.nq_bounds().empty());
  EXPECT_EQ(bounds.inf_l(), inf_l_);
  EXPECT_EQ(bounds.inf_u(), inf_u_);
}

TEST_F(TestContextBoundVector, AddLBound) {
  const mpq_class value{1};
  const Literal exp{Variable{"exp", Variable::Type::BOOLEAN}, true};
  empty_bounds_.AddBound(value, LpColBound::L, {exp});
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 1);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(empty_bounds_.bounds().size(), 1u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), value);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
  const auto [b_value, b_type, b_exp] = empty_bounds_.bounds()[0];
  EXPECT_EQ(*b_value, value);
  EXPECT_EQ(b_type, LpColBound::L);
  EXPECT_EQ(b_exp, std::set{exp});
  EXPECT_TRUE(empty_bounds_.nq_bounds().empty());
}

TEST_F(TestContextBoundVector, AddUBound) {
  const mpq_class value{1};
  const Literal exp{Variable{"exp", Variable::Type::BOOLEAN}, true};
  empty_bounds_.AddBound(value, LpColBound::U, {exp});
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 1);
  EXPECT_EQ(empty_bounds_.bounds().size(), 1u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), value);
  const auto [b_value, b_type, b_exp] = empty_bounds_.bounds()[0];
  EXPECT_EQ(*b_value, value);
  EXPECT_EQ(b_type, LpColBound::U);
  EXPECT_EQ(b_exp, std::set{exp});
  EXPECT_TRUE(empty_bounds_.nq_bounds().empty());
}

TEST_F(TestContextBoundVector, AddBBound) {
  const mpq_class value{1};
  const Literal exp{Variable{"exp", Variable::Type::BOOLEAN}, true};
  empty_bounds_.AddBound(value, LpColBound::B, {exp});
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 1);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 1);
  EXPECT_EQ(empty_bounds_.bounds().size(), 2u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), value);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), value);
  const auto [b_value, b_type, b_exp] = empty_bounds_.bounds()[0];
  EXPECT_EQ(*b_value, value);
  EXPECT_EQ(b_type, LpColBound::L);
  EXPECT_EQ(b_exp, std::set{exp});
  const auto [b_value2, b_type2, b_exp2] = empty_bounds_.bounds()[1];
  EXPECT_EQ(*b_value2, value);
  EXPECT_EQ(b_type2, LpColBound::U);
  EXPECT_EQ(b_exp2, std::set{exp});
  EXPECT_TRUE(empty_bounds_.nq_bounds().empty());
}

TEST_F(TestContextBoundVector, AddSLBound) {
  const mpq_class value{1};
  const Literal exp{Variable{"exp", Variable::Type::BOOLEAN}, true};
  empty_bounds_.AddBound(value, LpColBound::SL, {exp});
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 1);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(empty_bounds_.bounds().size(), 1u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), value);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
  const auto [b_value, b_type, b_exp] = empty_bounds_.bounds()[0];
  EXPECT_EQ(*b_value, value);
  EXPECT_EQ(b_type, LpColBound::SL);
  EXPECT_EQ(b_exp, std::set{exp});
  EXPECT_TRUE(empty_bounds_.nq_bounds().empty());
}

TEST_F(TestContextBoundVector, AddSUBound) {
  const mpq_class value{1};
  const Literal exp{Variable{"exp", Variable::Type::BOOLEAN}, true};
  empty_bounds_.AddBound(value, LpColBound::SU, {exp});
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 1);
  EXPECT_EQ(empty_bounds_.bounds().size(), 1u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), value);
  const auto [b_value, b_type, b_exp] = empty_bounds_.bounds()[0];
  EXPECT_EQ(*b_value, value);
  EXPECT_EQ(b_type, LpColBound::SU);
  EXPECT_EQ(b_exp, std::set{exp});
  EXPECT_TRUE(empty_bounds_.nq_bounds().empty());
}

TEST_F(TestContextBoundVector, AddDBound) {
  const mpq_class value{1};
  const Literal exp{Variable{"exp", Variable::Type::BOOLEAN}, true};
  empty_bounds_.AddBound(value, LpColBound::D, {exp});
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(empty_bounds_.bounds().size(), 0u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
  EXPECT_EQ(empty_bounds_.nq_bounds().size(), 1u);
  EXPECT_EQ(*empty_bounds_.nq_bounds().begin(), Bound(&value, LpColBound::D, {exp}));
}

TEST_F(TestContextBoundVector, EmptyActiveBound) {
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_TRUE(it.empty());
}
TEST_F(TestContextBoundVector, EmptyActiveBounds) {
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_TRUE(it.empty());
}
TEST_F(TestContextBoundVector, OnlyNqActiveBound) {
  empty_bounds_.AddBound(val_[0], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[0], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.nq_bounds_size(), 3u);
  EXPECT_TRUE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().begin());
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend());
}
TEST_F(TestContextBoundVector, OnlyNqActiveBounds) {
  empty_bounds_.AddBound(val_[0], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[0], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.nq_bounds_size(), 3u);
  EXPECT_TRUE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().begin());
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend());
}
TEST_F(TestContextBoundVector, NoNqActiveBound) {
  auto it = bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() - 1);
  EXPECT_EQ(it.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() + 1);
}
TEST_F(TestContextBoundVector, NoNqActiveBounds) {
  auto it = bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() - 1);
  EXPECT_EQ(it.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() + 1);
}
TEST_F(TestContextBoundVector, OnlyLowerBoundsActiveBound) {
  const std::set<Literal> eq_exp = exp();
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SL, eq_exp);
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cend() - 1);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
  EXPECT_EQ(*it, Bound(&val_[3], LpColBound::SL, eq_exp));
}
TEST_F(TestContextBoundVector, OnlyLowerBoundsActiveBounds) {
  const std::set<Literal> eq_exp = exp(), eq_exp2 = exp();
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::L, eq_exp);
  empty_bounds_.AddBound(val_[3], LpColBound::SL, eq_exp2);
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cend() - 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
  EXPECT_EQ(*it, Bound(&val_[3], LpColBound::L, eq_exp));
  EXPECT_EQ(*(++it), Bound(&val_[3], LpColBound::SL, eq_exp2));
}
TEST_F(TestContextBoundVector, OnlyUpperBoundsActiveBound) {
  const std::set<Literal> eq_exp = exp();
  empty_bounds_.AddBound(val_[1], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SU, eq_exp);
  empty_bounds_.AddBound(val_[2], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, exp());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(*it, Bound(&val_[1], LpColBound::SU, eq_exp));
}
TEST_F(TestContextBoundVector, OnlyUpperBoundsActiveBounds) {
  const std::set<Literal> eq_exp = exp(), eq_exp2 = exp();
  empty_bounds_.AddBound(val_[1], LpColBound::U, eq_exp2);
  empty_bounds_.AddBound(val_[1], LpColBound::SU, eq_exp);
  empty_bounds_.AddBound(val_[2], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, exp());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(*it, Bound(&val_[1], LpColBound::SU, eq_exp));
  EXPECT_EQ(*(++it), Bound(&val_[1], LpColBound::U, eq_exp2));
}

TEST_F(TestContextBoundVector, NqBoundsActiveBound) {
  empty_bounds_.AddBound(val_[0], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[0], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[0], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::SU, exp());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 3u);
  EXPECT_EQ(it.nq_bounds_size(), 1u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 3);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 3);
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin() + 2);
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend() - 2);
}
TEST_F(TestContextBoundVector, NqBoundsActiveBounds) {
  empty_bounds_.AddBound(val_[0], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[0], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[0], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::SU, exp());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 5u);
  EXPECT_EQ(it.nq_bounds_size(), 1u);
  EXPECT_EQ(it.bounds_size(), 4u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 2);
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin() + 2);
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend() - 2);
}
TEST_F(TestContextBoundVector, NqBoundsActiveBoundLower) {
  empty_bounds_.AddBound(val_[0], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[0], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[0], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::D, exp());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 4u);
  EXPECT_EQ(it.nq_bounds_size(), 3u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 3);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin() + 2);
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend());
}
TEST_F(TestContextBoundVector, NqBoundsActiveBoundsLower) {
  empty_bounds_.AddBound(val_[0], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[0], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[0], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::D, exp());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 5u);
  EXPECT_EQ(it.nq_bounds_size(), 3u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin() + 2);
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend());
}
TEST_F(TestContextBoundVector, NqBoundsActiveBoundUpper) {
  empty_bounds_.AddBound(val_[0], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::SU, exp());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 4u);
  EXPECT_EQ(it.nq_bounds_size(), 3u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 3);
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin());
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend() - 2);
}
TEST_F(TestContextBoundVector, NqBoundsActiveBoundsUpper) {
  empty_bounds_.AddBound(val_[0], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::SU, exp());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 5u);
  EXPECT_EQ(it.nq_bounds_size(), 3u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 2);
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin());
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend() - 2);
}

TEST_F(TestContextBoundVector, PriorityEqBoundsActiveBoundOverLower) {
  const std::set<Literal> eq_exp = exp();
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::B, eq_exp);
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(*it.bounds().first, Bound(&val_[3], LpColBound::L, eq_exp));
  EXPECT_EQ(*(it.bounds().first + 1), Bound(&val_[3], LpColBound::U, eq_exp));
}
TEST_F(TestContextBoundVector, PriorityEqBoundsActiveBoundsOverLower) {
  const std::set<Literal> eq_exp = exp();
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::B, eq_exp);
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(*it.bounds().first, Bound(&val_[3], LpColBound::L, eq_exp));
  EXPECT_EQ(*(it.bounds().first + 1), Bound(&val_[3], LpColBound::U, eq_exp));
}
TEST_F(TestContextBoundVector, PriorityEqBoundActiveBoundsOverUpper) {
  const std::set<Literal> eq_exp = exp();
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::B, eq_exp);
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(*it.bounds().first, Bound(&val_[3], LpColBound::L, eq_exp));
  EXPECT_EQ(*(it.bounds().first + 1), Bound(&val_[3], LpColBound::U, eq_exp));
}
TEST_F(TestContextBoundVector, PriorityEqBoundsActiveBoundsOverUpper) {
  const std::set<Literal> eq_exp = exp();
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::B, eq_exp);
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(*it.bounds().first, Bound(&val_[3], LpColBound::L, eq_exp));
  EXPECT_EQ(*(it.bounds().first + 1), Bound(&val_[3], LpColBound::U, eq_exp));
}
TEST_F(TestContextBoundVector, EqBoundsActiveBound) {
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::B, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 3);
}
TEST_F(TestContextBoundVector, EqBoundsActiveBounds) {
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::B, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 7u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 7u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestContextBoundVector, LBBoundsActiveBound) {
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 2);
}
TEST_F(TestContextBoundVector, LBBoundsActiveBounds) {
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 5u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 5u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
}

TEST_F(TestContextBoundVector, AbsentGetActiveSingleBound) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, exp());
  auto it = empty_bounds_.GetActiveBound(val_[2] + mpq_class{1, 2});
  EXPECT_TRUE(it.empty());
}
TEST_F(TestContextBoundVector, AbsentGetActiveSingleBounds) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, exp());
  auto it = empty_bounds_.GetActiveBounds(val_[2] + mpq_class{1, 2});
  EXPECT_TRUE(it.empty());
}
TEST_F(TestContextBoundVector, NqGetActiveSingleBound) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, exp());
  auto it = empty_bounds_.GetActiveBound(val_[2]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.nq_bounds_size(), 1u);
  EXPECT_TRUE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin() + 1);
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend() - 1);
}
TEST_F(TestContextBoundVector, NqGetActiveSingleBounds) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, exp());
  auto it = empty_bounds_.GetActiveBounds(val_[2]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.nq_bounds_size(), 1u);
  EXPECT_TRUE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin() + 1);
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend() - 1);
}
TEST_F(TestContextBoundVector, EqGetActiveSingleBound) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::B, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  auto it = empty_bounds_.GetActiveBound(val_[2]);
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 1);
}
TEST_F(TestContextBoundVector, EqGetActiveSingleBounds) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::B, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  auto it = empty_bounds_.GetActiveBounds(val_[2]);
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 1);
}
TEST_F(TestContextBoundVector, StrictLowerGetActiveSingleBound) {
  const std::set<Literal> eq_exp = exp();
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, eq_exp);
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, exp());
  auto it = empty_bounds_.GetActiveBound(val_[1]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 2);
  EXPECT_EQ(*it, Bound(&val_[1], LpColBound::SL, eq_exp));
}
TEST_F(TestContextBoundVector, StrictLowerGetActiveSingleBounds) {
  const std::set<Literal> eq_exp = exp(), eq_exp2 = exp();
  empty_bounds_.AddBound(val_[1], LpColBound::L, eq_exp);
  empty_bounds_.AddBound(val_[1], LpColBound::SL, eq_exp2);
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, exp());
  auto it = empty_bounds_.GetActiveBounds(val_[1]);
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 2);
  EXPECT_EQ(*it, Bound(&val_[1], LpColBound::L, eq_exp));
  EXPECT_EQ(*(++it), Bound(&val_[1], LpColBound::SL, eq_exp2));
}
TEST_F(TestContextBoundVector, LowerGetActiveSingleBound) {
  const std::set<Literal> eq_exp = exp();
  empty_bounds_.AddBound(val_[1], LpColBound::L, eq_exp);
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, exp());
  auto it = empty_bounds_.GetActiveBound(val_[1]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 2);
  EXPECT_EQ(*it, Bound(&val_[1], LpColBound::L, eq_exp));
}
TEST_F(TestContextBoundVector, LowerGetActiveSingleBounds) {
  const std::set<Literal> eq_exp = exp();
  empty_bounds_.AddBound(val_[1], LpColBound::L, eq_exp);
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, exp());
  auto it = empty_bounds_.GetActiveBounds(val_[1]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 2);
  EXPECT_EQ(*it, Bound(&val_[1], LpColBound::L, eq_exp));
}
TEST_F(TestContextBoundVector, StrictUpperGetActiveSingleBound) {
  const std::set<Literal> eq_exp = exp();
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, eq_exp);
  auto it = empty_bounds_.GetActiveBound(val_[3]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 1);
  EXPECT_EQ(*it, Bound(&val_[3], LpColBound::SU, eq_exp));
}
TEST_F(TestContextBoundVector, StrictUpperGetActiveSingleBounds) {
  const std::set<Literal> eq_exp = exp(), eq_exp2 = exp();
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, eq_exp2);
  empty_bounds_.AddBound(val_[3], LpColBound::SU, eq_exp);
  auto it = empty_bounds_.GetActiveBounds(val_[3]);
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
  EXPECT_EQ(*it, Bound(&val_[3], LpColBound::SU, eq_exp));
  EXPECT_EQ(*(++it), Bound(&val_[3], LpColBound::U, eq_exp2));
}
TEST_F(TestContextBoundVector, UpperGetActiveSingleBound) {
  const std::set<Literal> eq_exp = exp();
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, eq_exp);
  auto it = empty_bounds_.GetActiveBound(val_[3]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
  EXPECT_EQ(*it, Bound(&val_[3], LpColBound::U, eq_exp));
}
TEST_F(TestContextBoundVector, UpperGetActiveSingleBounds) {
  const std::set<Literal> eq_exp = exp();
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, eq_exp);
  auto it = empty_bounds_.GetActiveBounds(val_[3]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
  EXPECT_EQ(*it, Bound(&val_[3], LpColBound::U, eq_exp));
}

TEST_F(TestContextBoundVector, SetBounds) {
  mpq_class lb{1};
  mpq_class ub{2};
  empty_bounds_.SetBounds(lb, ub);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), lb);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), ub);
}
TEST_F(TestContextBoundVector, SetLowerBound) {
  mpq_class lb{1};
  empty_bounds_.SetLowerBound(lb);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), lb);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
}
TEST_F(TestContextBoundVector, SetUpperBound) {
  mpq_class ub{2};
  empty_bounds_.SetUpperBound(ub);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), ub);
}

TEST_F(TestContextBoundVector, SetBoundsUnchanged) {
  empty_bounds_.SetBounds(inf_l_ - 1, inf_u_ + 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
}
TEST_F(TestContextBoundVector, SetBoundsUnchangedLower) {
  mpq_class ub{2};
  empty_bounds_.SetBounds(inf_l_ - 1, ub);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), ub);
}
TEST_F(TestContextBoundVector, SetBoundsUnchangedUpper) {
  mpq_class lb{1};
  empty_bounds_.SetBounds(lb, inf_u_ + 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), lb);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
}
TEST_F(TestContextBoundVector, SetLowerBoundUnchanged) {
  empty_bounds_.SetLowerBound(inf_l_ - 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
}
TEST_F(TestContextBoundVector, SetUpperBoundUnchanged) {
  empty_bounds_.SetUpperBound(inf_u_ + 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
}

TEST_F(TestContextBoundVector, SetBoundsInvalid) {
  mpq_class lb{1};
  mpq_class ub{2};
  EXPECT_THROW(empty_bounds_.SetBounds(ub, lb), std::runtime_error);
}
TEST_F(TestContextBoundVector, SetLowerBoundInvalid) {
  EXPECT_THROW(empty_bounds_.SetLowerBound(inf_u_ + 1), std::runtime_error);
}
TEST_F(TestContextBoundVector, SetUpperBoundInvalid) {
  EXPECT_THROW(empty_bounds_.SetUpperBound(inf_l_ - 1), std::runtime_error);
}

TEST_F(TestContextBoundVector, Clear) {
  bounds_.Clear();
  EXPECT_EQ(bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(bounds_.bounds().size(), 0u);
  EXPECT_EQ(bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(bounds_.active_upper_bound(), inf_u_);
  EXPECT_EQ(bounds_.inf_l(), inf_l_);
  EXPECT_EQ(bounds_.inf_u(), inf_u_);
}

TEST_F(TestContextBoundVector, IsActiveEquality) { EXPECT_TRUE(bounds_.IsActiveEquality(3)); }

TEST_F(TestContextBoundVector, IsActiveEqualityLUBounds) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::U, exp());
  EXPECT_TRUE(empty_bounds_.IsActiveEquality(1));
}

TEST_F(TestContextBoundVector, IsLowerBound) {
  EXPECT_TRUE(bounds_.IsLowerBound(1));
  EXPECT_TRUE(bounds_.IsLowerBound(2));
  EXPECT_TRUE(bounds_.IsLowerBound(3));
  EXPECT_FALSE(bounds_.IsLowerBound(4));
  EXPECT_FALSE(bounds_.IsLowerBound(5));
}

TEST_F(TestContextBoundVector, IsUpperBound) {
  EXPECT_FALSE(bounds_.IsUpperBound(1));
  EXPECT_FALSE(bounds_.IsUpperBound(2));
  EXPECT_TRUE(bounds_.IsUpperBound(3));
  EXPECT_TRUE(bounds_.IsUpperBound(4));
  EXPECT_TRUE(bounds_.IsUpperBound(5));
}

TEST_F(TestContextBoundVector, IsLowerSingle) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  EXPECT_TRUE(empty_bounds_.IsLowerBound(1));
  EXPECT_FALSE(empty_bounds_.IsUpperBound(1));
}

TEST_F(TestContextBoundVector, IsLowerBack) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  EXPECT_TRUE(empty_bounds_.IsLowerBound(3));
  EXPECT_FALSE(empty_bounds_.IsUpperBound(3));
}

TEST_F(TestContextBoundVector, IsUpperSingle) {
  empty_bounds_.AddBound(val_[1], LpColBound::U, exp());
  EXPECT_TRUE(empty_bounds_.IsUpperBound(1));
  EXPECT_FALSE(empty_bounds_.IsLowerBound(1));
}

TEST_F(TestContextBoundVector, IsUpperFront) {
  empty_bounds_.AddBound(val_[1], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  EXPECT_TRUE(empty_bounds_.IsUpperBound(1));
  EXPECT_FALSE(empty_bounds_.IsLowerBound(1));
}

TEST_F(TestContextBoundVector, IsUpperIsLowerEqualityExplicit) {
  empty_bounds_.AddBound(val_[1], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  EXPECT_TRUE(empty_bounds_.IsUpperBound(1));
  EXPECT_TRUE(empty_bounds_.IsLowerBound(1));
}

TEST_F(TestContextBoundVector, IsUpperIsLowerEqualityImplicit) {
  empty_bounds_.AddBound(val_[1], LpColBound::B, exp());
  EXPECT_TRUE(empty_bounds_.IsUpperBound(1));
  EXPECT_TRUE(empty_bounds_.IsLowerBound(1));
}

TEST_F(TestContextBoundVector, AddLowerOnEdge) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::L, exp());
  EXPECT_FALSE(violation);
}
TEST_F(TestContextBoundVector, AddUpperOnEdge) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::U, exp());
  EXPECT_FALSE(violation);
}
TEST_F(TestContextBoundVector, AddEqualOnEdge) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::B, exp());
  EXPECT_FALSE(violation);
}

TEST_F(TestContextBoundVector, ViolationLowerOverUpperLeft) {
  const auto violation = bounds_.AddBound({35, 10}, LpColBound::L, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend() - 2);
}
TEST_F(TestContextBoundVector, ViolationLowerOverUpperMiddle) {
  const auto violation = bounds_.AddBound({45, 10}, LpColBound::L, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend() - 1);
}
TEST_F(TestContextBoundVector, ViolationLowerOverUpperRight) {
  const auto violation = bounds_.AddBound(val_[6], LpColBound::L, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend());
}

TEST_F(TestContextBoundVector, ViolationUpperOverLowerLeft) {
  const auto violation = bounds_.AddBound(val_[0], LpColBound::U, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestContextBoundVector, ViolationUpperOverLowerMiddle) {
  const auto violation = bounds_.AddBound({15, 10}, LpColBound::U, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestContextBoundVector, ViolationUpperOverLowerRight) {
  const auto violation = bounds_.AddBound({25, 10}, LpColBound::U, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}

TEST_F(TestContextBoundVector, ViolationEqualOverLowerLeft) {
  const auto violation = bounds_.AddBound(val_[0], LpColBound::B, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestContextBoundVector, ViolationEqualOverLowerMiddle) {
  const auto violation = bounds_.AddBound({15, 10}, LpColBound::B, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestContextBoundVector, ViolationEqualOverLowerRight) {
  const auto violation = bounds_.AddBound({25, 10}, LpColBound::B, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestContextBoundVector, ViolationEqualOverUpperLeft) {
  const auto violation = bounds_.AddBound({35, 10}, LpColBound::B, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend() - 2);
}
TEST_F(TestContextBoundVector, ViolationEqualOverUpperMiddle) {
  const auto violation = bounds_.AddBound({45, 10}, LpColBound::B, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend() - 1);
}
TEST_F(TestContextBoundVector, ViolationEqualOverUpperRight) {
  const auto violation = bounds_.AddBound(val_[6], LpColBound::B, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend());
}
TEST_F(TestContextBoundVector, ViolationEqualOverMultipleLower) {
  empty_bounds_.AddBound(val_[0], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::L, exp());
  const auto violation = empty_bounds_.AddBound(val_[1], LpColBound::B, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestContextBoundVector, ViolationEqualOverMultipleUpper) {
  empty_bounds_.AddBound(val_[0], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[1], LpColBound::SU, exp());
  empty_bounds_.AddBound(val_[2], LpColBound::U, exp());
  const auto violation = empty_bounds_.AddBound(val_[1], LpColBound::B, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cbegin() + 2);
}

TEST_F(TestContextBoundVector, ViolationStrictLowerOverEquality) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::SL, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() + 1);
}
TEST_F(TestContextBoundVector, ViolationStrictUpperOverEquality) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::SU, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() - 1);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestContextBoundVector, ViolationStrictInequalityOverEquality) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::D, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() - 1);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() + 1);
}

TEST_F(TestContextBoundVector, ViolationLowerOverStrictInequality) {
  empty_bounds_.AddBound(val_[2], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::U, exp());
  const auto violation = empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 1u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 1);
  EXPECT_EQ(violation.nq_bounds_size(), 1u);
  EXPECT_EQ(violation.nq_bounds().first, empty_bounds_.nq_bounds().cbegin());
  EXPECT_EQ(violation.nq_bounds().second, empty_bounds_.nq_bounds().cend());
}

TEST_F(TestContextBoundVector, ViolationUpperOverStrictInequality) {
  empty_bounds_.AddBound(val_[2], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::L, exp());
  empty_bounds_.AddBound(val_[3], LpColBound::D, exp());
  empty_bounds_.AddBound(val_[4], LpColBound::U, exp());
  const auto violation = empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 1u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 1);
  EXPECT_EQ(violation.nq_bounds_size(), 1u);
  EXPECT_EQ(violation.nq_bounds().first, empty_bounds_.nq_bounds().cbegin());
  EXPECT_EQ(violation.nq_bounds().second, empty_bounds_.nq_bounds().cend());
}

TEST_F(TestContextBoundVector, ViolationUpperOverStrictLower) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, exp()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::U, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cbegin() + 1);
}

TEST_F(TestContextBoundVector, ViolationLowerOverStrictUpper) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SU, exp()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::L, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cbegin() + 1);
}

TEST_F(TestContextBoundVector, ViolationUpperOverStrictLowerStandardViolationAdditionalElement) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SL, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::L, exp()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::U, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 4u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestContextBoundVector, ViolationLowerOverStrictUpperStandardViolationAdditionalElement) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SU, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::U, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, exp()));
  auto violation = empty_bounds_.AddBound(val_[2], LpColBound::L, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 4u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 2);
}
TEST_F(TestContextBoundVector, ViolationEqualOverStrictLowerStandardViolationAdditionalElement) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SL, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::L, exp()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::B, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 4u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestContextBoundVector, ViolationEqualOverStrictUpperStandardViolationAdditionalElement) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SU, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::U, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, exp()));
  auto violation = empty_bounds_.AddBound(val_[2], LpColBound::B, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 4u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 2);
}

TEST_F(TestContextBoundVector, ViolationUpperOverStrictLowerStandardViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, exp()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::U, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestContextBoundVector, ViolationLowerOverStrictUpperStandardViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, exp()));
  auto violation = empty_bounds_.AddBound(val_[2], LpColBound::L, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 2);
}
TEST_F(TestContextBoundVector, ViolationEqualOverStrictLowerStandardViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, exp()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::B, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestContextBoundVector, ViolationEqualOverStrictUpperStandardViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, exp()));
  auto violation = empty_bounds_.AddBound(val_[2], LpColBound::B, exp());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 2);
}

TEST_F(TestContextBoundVector, ViolationUpperOverStrictLowerStandardNoViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SL, exp()));
  auto violation = empty_bounds_.AddBound(val_[3], LpColBound::U, exp());
  EXPECT_FALSE(violation);
}

TEST_F(TestContextBoundVector, ViolationLowerOverStrictUpperStandardNoViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SU, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, exp()));
  auto violation = empty_bounds_.AddBound(val_[0], LpColBound::L, exp());
  EXPECT_FALSE(violation);
}

TEST_F(TestContextBoundVector, ViolationEqualOverStrictLowerStandardNoViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SL, exp()));
  auto violation = empty_bounds_.AddBound(val_[3], LpColBound::B, exp());
  EXPECT_FALSE(violation);
}
TEST_F(TestContextBoundVector, ViolationEqualOverStrictUpperStandardNoViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SU, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, exp()));
  auto violation = empty_bounds_.AddBound(val_[0], LpColBound::B, exp());
  EXPECT_FALSE(violation);
}

TEST_F(TestContextBoundVector, IsBoundedEmpty) {
  EXPECT_FALSE(empty_bounds_.IsBounded());
  EXPECT_FALSE(empty_bounds_.IsUpperBounded());
  EXPECT_FALSE(empty_bounds_.IsLowerBounded());
}
TEST_F(TestContextBoundVector, IsStrictLowerBounded) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, exp()));
  EXPECT_FALSE(empty_bounds_.IsBounded());
  EXPECT_FALSE(empty_bounds_.IsUpperBounded());
  EXPECT_TRUE(empty_bounds_.IsLowerBounded());
}
TEST_F(TestContextBoundVector, IsLowerBounded) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, exp()));
  EXPECT_FALSE(empty_bounds_.IsBounded());
  EXPECT_FALSE(empty_bounds_.IsUpperBounded());
  EXPECT_TRUE(empty_bounds_.IsLowerBounded());
}
TEST_F(TestContextBoundVector, IsStrictUpperBounded) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SU, exp()));
  EXPECT_FALSE(empty_bounds_.IsBounded());
  EXPECT_TRUE(empty_bounds_.IsUpperBounded());
  EXPECT_FALSE(empty_bounds_.IsLowerBounded());
}
TEST_F(TestContextBoundVector, IsUpperBounded) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::U, exp()));
  EXPECT_FALSE(empty_bounds_.IsBounded());
  EXPECT_TRUE(empty_bounds_.IsUpperBounded());
  EXPECT_FALSE(empty_bounds_.IsLowerBounded());
}
TEST_F(TestContextBoundVector, IsBounded) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::B, exp()));
  EXPECT_TRUE(empty_bounds_.IsBounded());
  EXPECT_TRUE(empty_bounds_.IsUpperBounded());
  EXPECT_TRUE(empty_bounds_.IsLowerBounded());
}
TEST_F(TestContextBoundVector, IsBoundedMultiple) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, exp()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, exp()));
  EXPECT_TRUE(empty_bounds_.IsBounded());
  EXPECT_TRUE(empty_bounds_.IsUpperBounded());
  EXPECT_TRUE(empty_bounds_.IsLowerBounded());
}

TEST_F(TestContextBoundVector, Stdout) { EXPECT_NO_THROW(std::cout << bounds_ << std::endl); }