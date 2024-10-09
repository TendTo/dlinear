/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "dlinear/solver/BoundVector.h"

using dlinear::Bound;
using dlinear::BoundVector;
using dlinear::Literal;
using dlinear::LpColBound;
using dlinear::Variable;

class TestBoundVector : public ::testing::Test {
 protected:
  const mpq_class inf_l_{-100};
  const mpq_class inf_u_{100};
  int idx_{0};
  BoundVector bounds_;
  BoundVector empty_bounds_;
  const mpq_class val_[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
  Literal exp1_, exp2_, exp3_, exp4_, exp5_;

  TestBoundVector() : bounds_{inf_l_, inf_u_}, empty_bounds_{inf_l_, inf_u_} {
    bounds_.AddBound(val_[1], LpColBound::L, {exp1_});
    bounds_.AddBound(val_[2], LpColBound::L, {exp2_});
    bounds_.AddBound(val_[3], LpColBound::B, {exp3_});
    bounds_.AddBound(val_[4], LpColBound::U, {exp4_});
    bounds_.AddBound(val_[5], LpColBound::U, {exp5_});
  }

  Literal lit() {
    return Literal{Variable{"exp" + std::to_string(idx_++), Variable::Type::BOOLEAN}, static_cast<bool>(idx_ & 1)};
  }
};

TEST_F(TestBoundVector, Constructor) {
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

TEST_F(TestBoundVector, AddLBound) {
  const mpq_class value{1};
  const Literal exp{Variable{"exp", Variable::Type::BOOLEAN}, true};
  empty_bounds_.AddBound(value, LpColBound::L, {exp});
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 1);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(empty_bounds_.bounds().size(), 1u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), value);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
  const auto [b_value, b_type, b_lit, b_exp] = empty_bounds_.bounds()[0];
  EXPECT_EQ(*b_value, value);
  EXPECT_EQ(b_type, LpColBound::L);
  EXPECT_EQ(b_lit, exp);
  EXPECT_EQ(b_exp, std::set<Literal>{});
  EXPECT_TRUE(empty_bounds_.nq_bounds().empty());
}

TEST_F(TestBoundVector, AddUBound) {
  const mpq_class value{1};
  const Literal exp{Variable{"exp", Variable::Type::BOOLEAN}, true};
  empty_bounds_.AddBound(value, LpColBound::U, {exp});
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 1);
  EXPECT_EQ(empty_bounds_.bounds().size(), 1u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), value);
  const auto [b_value, b_type, b_lit, b_exp] = empty_bounds_.bounds()[0];
  EXPECT_EQ(*b_value, value);
  EXPECT_EQ(b_type, LpColBound::U);
  EXPECT_EQ(b_lit, exp);
  EXPECT_EQ(b_exp, std::set<Literal>{});
  EXPECT_TRUE(empty_bounds_.nq_bounds().empty());
}

TEST_F(TestBoundVector, AddBBound) {
  const mpq_class value{1};
  const Literal exp{Variable{"exp", Variable::Type::BOOLEAN}, true};
  empty_bounds_.AddBound(value, LpColBound::B, {exp});
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 1);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 1);
  EXPECT_EQ(empty_bounds_.bounds().size(), 2u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), value);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), value);
  const auto [b_value, b_type, b_lit, b_exp] = empty_bounds_.bounds()[0];
  EXPECT_EQ(*b_value, value);
  EXPECT_EQ(b_type, LpColBound::L);
  EXPECT_EQ(b_lit, exp);
  EXPECT_EQ(b_exp, std::set<Literal>{});
  const auto [b_value2, b_type2, b_lit2, b_exp2] = empty_bounds_.bounds()[1];
  EXPECT_EQ(*b_value2, value);
  EXPECT_EQ(b_type2, LpColBound::U);
  EXPECT_EQ(b_lit2, exp);
  EXPECT_EQ(b_exp2, std::set<Literal>{});
  EXPECT_TRUE(empty_bounds_.nq_bounds().empty());
}

TEST_F(TestBoundVector, AddSLBound) {
  const mpq_class value{1};
  const Literal exp{Variable{"exp", Variable::Type::BOOLEAN}, true};
  empty_bounds_.AddBound(value, LpColBound::SL, {exp});
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 1);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(empty_bounds_.bounds().size(), 1u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), value);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
  const auto [b_value, b_type, b_lit, b_exp] = empty_bounds_.bounds()[0];
  EXPECT_EQ(*b_value, value);
  EXPECT_EQ(b_type, LpColBound::SL);
  EXPECT_EQ(b_lit, exp);
  EXPECT_EQ(b_exp, std::set<Literal>{});
  EXPECT_TRUE(empty_bounds_.nq_bounds().empty());
}

TEST_F(TestBoundVector, AddSUBound) {
  const mpq_class value{1};
  const Literal exp{Variable{"exp", Variable::Type::BOOLEAN}, true};
  empty_bounds_.AddBound(value, LpColBound::SU, {exp});
  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 1);
  EXPECT_EQ(empty_bounds_.bounds().size(), 1u);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), value);
  const auto [b_value, b_type, b_lit, b_exp] = empty_bounds_.bounds()[0];
  EXPECT_EQ(*b_value, value);
  EXPECT_EQ(b_type, LpColBound::SU);
  EXPECT_EQ(b_lit, exp);
  EXPECT_EQ(b_exp, std::set<Literal>{});
  EXPECT_TRUE(empty_bounds_.nq_bounds().empty());
}

TEST_F(TestBoundVector, AddDBound) {
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

TEST_F(TestBoundVector, EmptyActiveBound) {
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_TRUE(it.empty());
}
TEST_F(TestBoundVector, EmptyActiveBounds) {
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_TRUE(it.empty());
}
TEST_F(TestBoundVector, OnlyNqActiveBound) {
  empty_bounds_.AddBound(val_[0], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[0], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.nq_bounds_size(), 3u);
  EXPECT_TRUE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().begin());
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend());
}
TEST_F(TestBoundVector, OnlyNqActiveBounds) {
  empty_bounds_.AddBound(val_[0], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[0], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.nq_bounds_size(), 3u);
  EXPECT_TRUE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().begin());
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend());
}
TEST_F(TestBoundVector, NoNqActiveBound) {
  auto it = bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() - 1);
  EXPECT_EQ(it.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() + 1);
}
TEST_F(TestBoundVector, NoNqActiveBounds) {
  auto it = bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() - 1);
  EXPECT_EQ(it.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() + 1);
}
TEST_F(TestBoundVector, OnlyLowerBoundsActiveBound) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SL, eq_exp);
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cend() - 1);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
  EXPECT_EQ(*it, Bound(&val_[3], LpColBound::SL, eq_exp));
}
TEST_F(TestBoundVector, OnlyLowerBoundsActiveBounds) {
  const Literal eq_exp = lit(), eq_exp2 = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::L, lit());
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
TEST_F(TestBoundVector, OnlyUpperBoundsActiveBound) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SU, eq_exp);
  empty_bounds_.AddBound(val_[2], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, lit());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(*it, Bound(&val_[1], LpColBound::SU, eq_exp));
}
TEST_F(TestBoundVector, OnlyUpperBoundsActiveBounds) {
  const Literal eq_exp = lit(), eq_exp2 = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::U, eq_exp2);
  empty_bounds_.AddBound(val_[1], LpColBound::SU, eq_exp);
  empty_bounds_.AddBound(val_[2], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, lit());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(*it, Bound(&val_[1], LpColBound::SU, eq_exp));
  EXPECT_EQ(*(++it), Bound(&val_[1], LpColBound::U, eq_exp2));
}

TEST_F(TestBoundVector, NqBoundsActiveBound) {
  empty_bounds_.AddBound(val_[0], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[0], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[0], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::SU, lit());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 3u);
  EXPECT_EQ(it.nq_bounds_size(), 1u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 3);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 3);
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin() + 2);
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend() - 2);
}
TEST_F(TestBoundVector, NqBoundsActiveBounds) {
  empty_bounds_.AddBound(val_[0], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[0], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[0], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::SU, lit());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 5u);
  EXPECT_EQ(it.nq_bounds_size(), 1u);
  EXPECT_EQ(it.bounds_size(), 4u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 2);
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin() + 2);
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend() - 2);
}
TEST_F(TestBoundVector, NqBoundsActiveBoundLower) {
  empty_bounds_.AddBound(val_[0], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[0], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[0], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::D, lit());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 4u);
  EXPECT_EQ(it.nq_bounds_size(), 3u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 3);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin() + 2);
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend());
}
TEST_F(TestBoundVector, NqBoundsActiveBoundsLower) {
  empty_bounds_.AddBound(val_[0], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[0], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[0], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::D, lit());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 5u);
  EXPECT_EQ(it.nq_bounds_size(), 3u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin() + 2);
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend());
}
TEST_F(TestBoundVector, NqBoundsActiveBoundUpper) {
  empty_bounds_.AddBound(val_[0], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::SU, lit());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 4u);
  EXPECT_EQ(it.nq_bounds_size(), 3u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 3);
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin());
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend() - 2);
}
TEST_F(TestBoundVector, NqBoundsActiveBoundsUpper) {
  empty_bounds_.AddBound(val_[0], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::SU, lit());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 5u);
  EXPECT_EQ(it.nq_bounds_size(), 3u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 2);
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin());
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend() - 2);
}

TEST_F(TestBoundVector, PriorityEqBoundsActiveBoundOverLower) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::B, eq_exp);
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(*it.bounds().first, Bound(&val_[3], LpColBound::L, eq_exp));
  EXPECT_EQ(*(it.bounds().first + 1), Bound(&val_[3], LpColBound::U, eq_exp));
}
TEST_F(TestBoundVector, PriorityEqBoundsActiveBoundsOverLower) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::B, eq_exp);
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(*it.bounds().first, Bound(&val_[3], LpColBound::L, eq_exp));
  EXPECT_EQ(*(it.bounds().first + 1), Bound(&val_[3], LpColBound::U, eq_exp));
}
TEST_F(TestBoundVector, PriorityEqBoundActiveBoundsOverUpper) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::B, eq_exp);
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(*it.bounds().first, Bound(&val_[3], LpColBound::L, eq_exp));
  EXPECT_EQ(*(it.bounds().first + 1), Bound(&val_[3], LpColBound::U, eq_exp));
}
TEST_F(TestBoundVector, PriorityEqBoundsActiveBoundsOverUpper) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::B, eq_exp);
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(*it.bounds().first, Bound(&val_[3], LpColBound::L, eq_exp));
  EXPECT_EQ(*(it.bounds().first + 1), Bound(&val_[3], LpColBound::U, eq_exp));
}
TEST_F(TestBoundVector, EqBoundsActiveBound) {
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::B, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 3);
}
TEST_F(TestBoundVector, EqBoundsActiveBounds) {
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::B, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 7u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 7u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestBoundVector, LBBoundsActiveBound) {
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  auto it = empty_bounds_.GetActiveBound();
  EXPECT_EQ(it.size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 2);
}
TEST_F(TestBoundVector, LBBoundsActiveBounds) {
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  auto it = empty_bounds_.GetActiveBounds();
  EXPECT_EQ(it.size(), 5u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds_size(), 5u);
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
}

TEST_F(TestBoundVector, AbsentGetActiveSingleBound) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, lit());
  auto it = empty_bounds_.GetActiveBound(val_[2] + mpq_class{1, 2});
  EXPECT_TRUE(it.empty());
}
TEST_F(TestBoundVector, AbsentGetActiveSingleBounds) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, lit());
  auto it = empty_bounds_.GetActiveBounds(val_[2] + mpq_class{1, 2});
  EXPECT_TRUE(it.empty());
}
TEST_F(TestBoundVector, NqGetActiveSingleBound) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, lit());
  auto it = empty_bounds_.GetActiveBound(val_[2]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.nq_bounds_size(), 1u);
  EXPECT_TRUE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin() + 1);
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend() - 1);
}
TEST_F(TestBoundVector, NqGetActiveSingleBounds) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, lit());
  auto it = empty_bounds_.GetActiveBounds(val_[2]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.nq_bounds_size(), 1u);
  EXPECT_TRUE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds().first, empty_bounds_.nq_bounds().cbegin() + 1);
  EXPECT_EQ(it.nq_bounds().second, empty_bounds_.nq_bounds().cend() - 1);
}
TEST_F(TestBoundVector, EqGetActiveSingleBound) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::B, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  auto it = empty_bounds_.GetActiveBound(val_[2]);
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 1);
}
TEST_F(TestBoundVector, EqGetActiveSingleBounds) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::B, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  auto it = empty_bounds_.GetActiveBounds(val_[2]);
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 1);
}
TEST_F(TestBoundVector, StrictLowerGetActiveSingleBound) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, eq_exp);
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, lit());
  auto it = empty_bounds_.GetActiveBound(val_[1]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 2);
  EXPECT_EQ(*it, Bound(&val_[1], LpColBound::SL, eq_exp));
}
TEST_F(TestBoundVector, StrictLowerGetActiveSingleBounds) {
  const Literal eq_exp = lit(), eq_exp2 = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::L, eq_exp);
  empty_bounds_.AddBound(val_[1], LpColBound::SL, eq_exp2);
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, lit());
  auto it = empty_bounds_.GetActiveBounds(val_[1]);
  EXPECT_EQ(it.size(), 2u);
  EXPECT_EQ(it.bounds_size(), 2u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 2);
  EXPECT_EQ(*it, Bound(&val_[1], LpColBound::L, eq_exp));
  EXPECT_EQ(*(++it), Bound(&val_[1], LpColBound::SL, eq_exp2));
}
TEST_F(TestBoundVector, LowerGetActiveSingleBound) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::L, eq_exp);
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, lit());
  auto it = empty_bounds_.GetActiveBound(val_[1]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 2);
  EXPECT_EQ(*it, Bound(&val_[1], LpColBound::L, eq_exp));
}
TEST_F(TestBoundVector, LowerGetActiveSingleBounds) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::L, eq_exp);
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, lit());
  auto it = empty_bounds_.GetActiveBounds(val_[1]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 2);
  EXPECT_EQ(*it, Bound(&val_[1], LpColBound::L, eq_exp));
}
TEST_F(TestBoundVector, StrictUpperGetActiveSingleBound) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::SU, eq_exp);
  auto it = empty_bounds_.GetActiveBound(val_[3]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend() - 1);
  EXPECT_EQ(*it, Bound(&val_[3], LpColBound::SU, eq_exp));
}
TEST_F(TestBoundVector, StrictUpperGetActiveSingleBounds) {
  const Literal eq_exp = lit(), eq_exp2 = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
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
TEST_F(TestBoundVector, UpperGetActiveSingleBound) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, eq_exp);
  auto it = empty_bounds_.GetActiveBound(val_[3]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
  EXPECT_EQ(*it, Bound(&val_[3], LpColBound::U, eq_exp));
}
TEST_F(TestBoundVector, UpperGetActiveSingleBounds) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, eq_exp);
  auto it = empty_bounds_.GetActiveBounds(val_[3]);
  EXPECT_EQ(it.size(), 1u);
  EXPECT_EQ(it.bounds_size(), 1u);
  EXPECT_TRUE(it.nq_bounds_empty());
  EXPECT_EQ(it.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(it.bounds().second, empty_bounds_.bounds().cend());
  EXPECT_EQ(*it, Bound(&val_[3], LpColBound::U, eq_exp));
}

TEST_F(TestBoundVector, SetBounds) {
  mpq_class lb{1};
  mpq_class ub{2};
  empty_bounds_.SetBounds(lb, ub);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), lb);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), ub);
}
TEST_F(TestBoundVector, SetLowerBound) {
  mpq_class lb{1};
  empty_bounds_.SetLowerBound(lb);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), lb);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
}
TEST_F(TestBoundVector, SetUpperBound) {
  mpq_class ub{2};
  empty_bounds_.SetUpperBound(ub);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), ub);
}

TEST_F(TestBoundVector, SetBoundsUnchanged) {
  empty_bounds_.SetBounds(inf_l_ - 1, inf_u_ + 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
}
TEST_F(TestBoundVector, SetBoundsUnchangedLower) {
  mpq_class ub{2};
  empty_bounds_.SetBounds(inf_l_ - 1, ub);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), ub);
}
TEST_F(TestBoundVector, SetBoundsUnchangedUpper) {
  mpq_class lb{1};
  empty_bounds_.SetBounds(lb, inf_u_ + 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), lb);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
}
TEST_F(TestBoundVector, SetLowerBoundUnchanged) {
  empty_bounds_.SetLowerBound(inf_l_ - 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
}
TEST_F(TestBoundVector, SetUpperBoundUnchanged) {
  empty_bounds_.SetUpperBound(inf_u_ + 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), inf_u_);
}

TEST_F(TestBoundVector, SetBoundsInvalid) {
  mpq_class lb{1};
  mpq_class ub{2};
  EXPECT_THROW(empty_bounds_.SetBounds(ub, lb), std::runtime_error);
}
TEST_F(TestBoundVector, SetLowerBoundInvalid) {
  EXPECT_THROW(empty_bounds_.SetLowerBound(inf_u_ + 1), std::runtime_error);
}
TEST_F(TestBoundVector, SetUpperBoundInvalid) {
  EXPECT_THROW(empty_bounds_.SetUpperBound(inf_l_ - 1), std::runtime_error);
}

TEST_F(TestBoundVector, Clear) {
  bounds_.Clear();
  EXPECT_EQ(bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(bounds_.bounds().size(), 0u);
  EXPECT_EQ(bounds_.active_lower_bound(), inf_l_);
  EXPECT_EQ(bounds_.active_upper_bound(), inf_u_);
  EXPECT_EQ(bounds_.inf_l(), inf_l_);
  EXPECT_EQ(bounds_.inf_u(), inf_u_);
}

TEST_F(TestBoundVector, IsActiveEquality) { EXPECT_TRUE(bounds_.IsActiveEquality(3)); }

TEST_F(TestBoundVector, IsActiveEqualityLUBounds) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::U, lit());
  EXPECT_TRUE(empty_bounds_.IsActiveEquality(1));
}

TEST_F(TestBoundVector, IsLowerBound) {
  EXPECT_TRUE(bounds_.IsLowerBound(1));
  EXPECT_TRUE(bounds_.IsLowerBound(2));
  EXPECT_TRUE(bounds_.IsLowerBound(3));
  EXPECT_FALSE(bounds_.IsLowerBound(4));
  EXPECT_FALSE(bounds_.IsLowerBound(5));
}

TEST_F(TestBoundVector, IsUpperBound) {
  EXPECT_FALSE(bounds_.IsUpperBound(1));
  EXPECT_FALSE(bounds_.IsUpperBound(2));
  EXPECT_TRUE(bounds_.IsUpperBound(3));
  EXPECT_TRUE(bounds_.IsUpperBound(4));
  EXPECT_TRUE(bounds_.IsUpperBound(5));
}

TEST_F(TestBoundVector, IsLowerSingle) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  EXPECT_TRUE(empty_bounds_.IsLowerBound(1));
  EXPECT_FALSE(empty_bounds_.IsUpperBound(1));
}

TEST_F(TestBoundVector, IsLowerBack) {
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  EXPECT_TRUE(empty_bounds_.IsLowerBound(3));
  EXPECT_FALSE(empty_bounds_.IsUpperBound(3));
}

TEST_F(TestBoundVector, IsUpperSingle) {
  empty_bounds_.AddBound(val_[1], LpColBound::U, lit());
  EXPECT_TRUE(empty_bounds_.IsUpperBound(1));
  EXPECT_FALSE(empty_bounds_.IsLowerBound(1));
}

TEST_F(TestBoundVector, IsUpperFront) {
  empty_bounds_.AddBound(val_[1], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  EXPECT_TRUE(empty_bounds_.IsUpperBound(1));
  EXPECT_FALSE(empty_bounds_.IsLowerBound(1));
}

TEST_F(TestBoundVector, IsUpperIsLowerEqualityExplicit) {
  empty_bounds_.AddBound(val_[1], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  EXPECT_TRUE(empty_bounds_.IsUpperBound(1));
  EXPECT_TRUE(empty_bounds_.IsLowerBound(1));
}

TEST_F(TestBoundVector, IsUpperIsLowerEqualityImplicit) {
  empty_bounds_.AddBound(val_[1], LpColBound::B, lit());
  EXPECT_TRUE(empty_bounds_.IsUpperBound(1));
  EXPECT_TRUE(empty_bounds_.IsLowerBound(1));
}

TEST_F(TestBoundVector, AddLowerOnEdge) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::L, lit());
  EXPECT_FALSE(violation);
}
TEST_F(TestBoundVector, AddUpperOnEdge) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::U, lit());
  EXPECT_FALSE(violation);
}
TEST_F(TestBoundVector, AddEqualOnEdge) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::B, lit());
  EXPECT_FALSE(violation);
}

TEST_F(TestBoundVector, ViolationLowerOverUpperLeft) {
  const auto violation = bounds_.AddBound({35, 10}, LpColBound::L, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend() - 2);
}
TEST_F(TestBoundVector, ViolationLowerOverUpperMiddle) {
  const auto violation = bounds_.AddBound({45, 10}, LpColBound::L, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend() - 1);
}
TEST_F(TestBoundVector, ViolationLowerOverUpperRight) {
  const auto violation = bounds_.AddBound(val_[6], LpColBound::L, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend());
}

TEST_F(TestBoundVector, ViolationUpperOverLowerLeft) {
  const auto violation = bounds_.AddBound(val_[0], LpColBound::U, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestBoundVector, ViolationUpperOverLowerMiddle) {
  const auto violation = bounds_.AddBound({15, 10}, LpColBound::U, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestBoundVector, ViolationUpperOverLowerRight) {
  const auto violation = bounds_.AddBound({25, 10}, LpColBound::U, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}

TEST_F(TestBoundVector, ViolationEqualOverLowerLeft) {
  const auto violation = bounds_.AddBound(val_[0], LpColBound::B, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestBoundVector, ViolationEqualOverLowerMiddle) {
  const auto violation = bounds_.AddBound({15, 10}, LpColBound::B, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestBoundVector, ViolationEqualOverLowerRight) {
  const auto violation = bounds_.AddBound({25, 10}, LpColBound::B, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestBoundVector, ViolationEqualOverUpperLeft) {
  const auto violation = bounds_.AddBound({35, 10}, LpColBound::B, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend() - 2);
}
TEST_F(TestBoundVector, ViolationEqualOverUpperMiddle) {
  const auto violation = bounds_.AddBound({45, 10}, LpColBound::B, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend() - 1);
}
TEST_F(TestBoundVector, ViolationEqualOverUpperRight) {
  const auto violation = bounds_.AddBound(val_[6], LpColBound::B, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cend());
}
TEST_F(TestBoundVector, ViolationEqualOverMultipleLower) {
  empty_bounds_.AddBound(val_[0], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SL, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::L, lit());
  const auto violation = empty_bounds_.AddBound(val_[1], LpColBound::B, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestBoundVector, ViolationEqualOverMultipleUpper) {
  empty_bounds_.AddBound(val_[0], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::SU, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::U, lit());
  const auto violation = empty_bounds_.AddBound(val_[1], LpColBound::B, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cbegin() + 2);
}

TEST_F(TestBoundVector, ViolationStrictLowerOverEquality) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::SL, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() + 1);
}
TEST_F(TestBoundVector, ViolationStrictUpperOverEquality) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::SU, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() - 1);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds());
}
TEST_F(TestBoundVector, ViolationStrictInequalityOverEquality) {
  const auto violation = bounds_.AddBound(val_[3], LpColBound::D, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() - 1);
  EXPECT_EQ(violation.bounds().second, bounds_.bounds().cbegin() + bounds_.n_lower_bounds() + 1);
}

TEST_F(TestBoundVector, ViolationLowerOverStrictInequality) {
  empty_bounds_.AddBound(val_[2], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::U, lit());
  const auto violation = empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 1u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 1);
  EXPECT_EQ(violation.nq_bounds_size(), 1u);
  EXPECT_EQ(violation.nq_bounds().first, empty_bounds_.nq_bounds().cbegin());
  EXPECT_EQ(violation.nq_bounds().second, empty_bounds_.nq_bounds().cend());
}

TEST_F(TestBoundVector, ViolationUpperOverStrictInequality) {
  empty_bounds_.AddBound(val_[2], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[3], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[4], LpColBound::U, lit());
  const auto violation = empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 1u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 1);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 1);
  EXPECT_EQ(violation.nq_bounds_size(), 1u);
  EXPECT_EQ(violation.nq_bounds().first, empty_bounds_.nq_bounds().cbegin());
  EXPECT_EQ(violation.nq_bounds().second, empty_bounds_.nq_bounds().cend());
}

TEST_F(TestBoundVector, ViolationUpperOverStrictLower) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, lit()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::U, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cbegin() + 1);
}

TEST_F(TestBoundVector, ViolationLowerOverStrictUpper) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SU, lit()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cbegin() + 1);
}

TEST_F(TestBoundVector, ViolationUpperOverStrictLowerStandardViolationAdditionalElement) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SL, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::L, lit()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::U, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 4u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestBoundVector, ViolationLowerOverStrictUpperStandardViolationAdditionalElement) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SU, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::U, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, lit()));
  auto violation = empty_bounds_.AddBound(val_[2], LpColBound::L, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 4u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 2);
}
TEST_F(TestBoundVector, ViolationEqualOverStrictLowerStandardViolationAdditionalElement) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SL, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::L, lit()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::B, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 4u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestBoundVector, ViolationEqualOverStrictUpperStandardViolationAdditionalElement) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SU, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::U, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, lit()));
  auto violation = empty_bounds_.AddBound(val_[2], LpColBound::B, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 4u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 2);
}

TEST_F(TestBoundVector, ViolationUpperOverStrictLowerStandardViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, lit()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::U, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestBoundVector, ViolationLowerOverStrictUpperStandardViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, lit()));
  auto violation = empty_bounds_.AddBound(val_[2], LpColBound::L, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 2);
}
TEST_F(TestBoundVector, ViolationEqualOverStrictLowerStandardViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, lit()));
  auto violation = empty_bounds_.AddBound(val_[1], LpColBound::B, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin() + 2);
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend());
}
TEST_F(TestBoundVector, ViolationEqualOverStrictUpperStandardViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, lit()));
  auto violation = empty_bounds_.AddBound(val_[2], LpColBound::B, lit());
  EXPECT_TRUE(violation);
  EXPECT_EQ(violation.bounds_size(), 2u);
  EXPECT_EQ(violation.bounds().first, empty_bounds_.bounds().cbegin());
  EXPECT_EQ(violation.bounds().second, empty_bounds_.bounds().cend() - 2);
}

TEST_F(TestBoundVector, ViolationUpperOverStrictLowerStandardNoViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SL, lit()));
  auto violation = empty_bounds_.AddBound(val_[3], LpColBound::U, lit());
  EXPECT_FALSE(violation);
}

TEST_F(TestBoundVector, ViolationLowerOverStrictUpperStandardNoViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SU, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, lit()));
  auto violation = empty_bounds_.AddBound(val_[0], LpColBound::L, lit());
  EXPECT_FALSE(violation);
}

TEST_F(TestBoundVector, ViolationEqualOverStrictLowerStandardNoViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SL, lit()));
  auto violation = empty_bounds_.AddBound(val_[3], LpColBound::B, lit());
  EXPECT_FALSE(violation);
}
TEST_F(TestBoundVector, ViolationEqualOverStrictUpperStandardNoViolation) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SU, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::SU, lit()));
  auto violation = empty_bounds_.AddBound(val_[0], LpColBound::B, lit());
  EXPECT_FALSE(violation);
}

TEST_F(TestBoundVector, IsBoundedEmpty) {
  EXPECT_FALSE(empty_bounds_.IsBounded());
  EXPECT_FALSE(empty_bounds_.IsUpperBounded());
  EXPECT_FALSE(empty_bounds_.IsLowerBounded());
}
TEST_F(TestBoundVector, IsStrictLowerBounded) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SL, lit()));
  EXPECT_FALSE(empty_bounds_.IsBounded());
  EXPECT_FALSE(empty_bounds_.IsUpperBounded());
  EXPECT_TRUE(empty_bounds_.IsLowerBounded());
}
TEST_F(TestBoundVector, IsLowerBounded) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, lit()));
  EXPECT_FALSE(empty_bounds_.IsBounded());
  EXPECT_FALSE(empty_bounds_.IsUpperBounded());
  EXPECT_TRUE(empty_bounds_.IsLowerBounded());
}
TEST_F(TestBoundVector, IsStrictUpperBounded) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::SU, lit()));
  EXPECT_FALSE(empty_bounds_.IsBounded());
  EXPECT_TRUE(empty_bounds_.IsUpperBounded());
  EXPECT_FALSE(empty_bounds_.IsLowerBounded());
}
TEST_F(TestBoundVector, IsUpperBounded) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::U, lit()));
  EXPECT_FALSE(empty_bounds_.IsBounded());
  EXPECT_TRUE(empty_bounds_.IsUpperBounded());
  EXPECT_FALSE(empty_bounds_.IsLowerBounded());
}
TEST_F(TestBoundVector, IsBounded) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::B, lit()));
  EXPECT_TRUE(empty_bounds_.IsBounded());
  EXPECT_TRUE(empty_bounds_.IsUpperBounded());
  EXPECT_TRUE(empty_bounds_.IsLowerBounded());
}
TEST_F(TestBoundVector, IsBoundedMultiple) {
  EXPECT_FALSE(empty_bounds_.AddBound(val_[1], LpColBound::L, lit()));
  EXPECT_FALSE(empty_bounds_.AddBound(val_[2], LpColBound::U, lit()));
  EXPECT_TRUE(empty_bounds_.IsBounded());
  EXPECT_TRUE(empty_bounds_.IsUpperBounded());
  EXPECT_TRUE(empty_bounds_.IsLowerBounded());
}

TEST_F(TestBoundVector, RemoveAbsentBound) { EXPECT_FALSE(empty_bounds_.RemoveBound(val_[1], LpColBound::L, lit())); }
TEST_F(TestBoundVector, RemoveLowerBoundUnbounded) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::L, eq_exp);
  EXPECT_TRUE(empty_bounds_.RemoveBound(val_[1], LpColBound::L, eq_exp));

  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 0);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), empty_bounds_.inf_l());
  EXPECT_FALSE(empty_bounds_.IsLowerBounded());
}
TEST_F(TestBoundVector, RemoveUpperBoundUnbounded) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::U, eq_exp);
  EXPECT_TRUE(empty_bounds_.RemoveBound(val_[1], LpColBound::U, eq_exp));

  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 0);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), empty_bounds_.inf_u());
  EXPECT_FALSE(empty_bounds_.IsUpperBounded());
}
TEST_F(TestBoundVector, RemoveUpperBoundChangeActiveBound) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[2], LpColBound::L, eq_exp);
  EXPECT_TRUE(empty_bounds_.RemoveBound(val_[2], LpColBound::L, eq_exp));

  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 1);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), val_[1]);
  EXPECT_TRUE(empty_bounds_.IsLowerBounded());
}
TEST_F(TestBoundVector, RemoveLowerBoundChangeActiveBound) {
  const Literal eq_exp = lit();
  empty_bounds_.AddBound(val_[1], LpColBound::U, eq_exp);
  empty_bounds_.AddBound(val_[2], LpColBound::U, lit());
  EXPECT_TRUE(empty_bounds_.RemoveBound(val_[1], LpColBound::U, eq_exp));

  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 1);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), val_[2]);
  EXPECT_TRUE(empty_bounds_.IsUpperBounded());
}
TEST_F(TestBoundVector, RemoveLowerBoundDuplicate) {
  const Literal eq_exp = lit();
  const Bound removed_bound{&val_[1], LpColBound::L, eq_exp, {eq_exp}};
  empty_bounds_.AddBound(val_[1], LpColBound::U, eq_exp);
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::L, eq_exp);
  empty_bounds_.AddBound(removed_bound);
  empty_bounds_.AddBound(val_[1], LpColBound::L, eq_exp, {lit()});
  empty_bounds_.AddBound(val_[1], LpColBound::L, lit());
  EXPECT_TRUE(empty_bounds_.RemoveBound(removed_bound));

  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 4);
  EXPECT_EQ(empty_bounds_.active_lower_bound(), val_[1]);
  EXPECT_TRUE(empty_bounds_.IsBounded());
  EXPECT_THAT(empty_bounds_.bounds(), ::testing::Not(::testing::Contains(removed_bound)));
}
TEST_F(TestBoundVector, RemoveUpperBoundDuplicate) {
  const Literal eq_exp = lit();
  const Bound removed_bound{&val_[1], LpColBound::U, eq_exp, {eq_exp}};
  empty_bounds_.AddBound(val_[1], LpColBound::L, eq_exp);
  empty_bounds_.AddBound(val_[1], LpColBound::U, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::U, eq_exp);
  empty_bounds_.AddBound(removed_bound);
  empty_bounds_.AddBound(val_[1], LpColBound::U, eq_exp, {lit()});
  empty_bounds_.AddBound(val_[1], LpColBound::U, lit());
  EXPECT_TRUE(empty_bounds_.RemoveBound(removed_bound));

  EXPECT_EQ(empty_bounds_.n_upper_bounds(), 4);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), val_[1]);
  EXPECT_TRUE(empty_bounds_.IsBounded());
  EXPECT_THAT(empty_bounds_.bounds(), ::testing::Not(::testing::Contains(removed_bound)));
}
TEST_F(TestBoundVector, RemoveEqBoundDuplicate) {
  const Literal eq_exp = lit();
  const Bound removed_bound{&val_[1], LpColBound::B, eq_exp, {eq_exp}};
  empty_bounds_.AddBound(val_[1], LpColBound::L, eq_exp);
  empty_bounds_.AddBound(val_[1], LpColBound::B, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::B, eq_exp);
  empty_bounds_.AddBound(removed_bound);
  empty_bounds_.AddBound(val_[1], LpColBound::B, eq_exp, {lit()});
  empty_bounds_.AddBound(val_[1], LpColBound::U, lit());

  Bound removed_lower_bound{removed_bound};
  removed_lower_bound.lp_bound = LpColBound::L;
  Bound removed_upper_bound{removed_bound};
  removed_upper_bound.lp_bound = LpColBound::U;

  EXPECT_THAT(empty_bounds_.bounds(), ::testing::Contains(removed_lower_bound));
  EXPECT_THAT(empty_bounds_.bounds(), ::testing::Contains(removed_upper_bound));

  EXPECT_TRUE(empty_bounds_.RemoveBound(removed_bound));

  EXPECT_EQ(empty_bounds_.n_lower_bounds(), 4);
  EXPECT_EQ(empty_bounds_.active_upper_bound(), val_[1]);
  EXPECT_TRUE(empty_bounds_.IsBounded());
  EXPECT_THAT(empty_bounds_.bounds(), ::testing::Not(::testing::Contains(removed_lower_bound)));
  EXPECT_THAT(empty_bounds_.bounds(), ::testing::Not(::testing::Contains(removed_upper_bound)));
}
TEST_F(TestBoundVector, RemoveNqBoundDuplicate) {
  const Literal eq_exp = lit();
  const Bound removed_bound{&val_[1], LpColBound::D, eq_exp, {eq_exp}};
  empty_bounds_.AddBound(val_[1], LpColBound::D, eq_exp);
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  empty_bounds_.AddBound(val_[1], LpColBound::D, eq_exp);
  empty_bounds_.AddBound(removed_bound);
  empty_bounds_.AddBound(val_[1], LpColBound::D, eq_exp, {lit()});
  empty_bounds_.AddBound(val_[1], LpColBound::D, lit());
  EXPECT_THAT(empty_bounds_.nq_bounds(), ::testing::Contains(removed_bound));

  EXPECT_TRUE(empty_bounds_.RemoveBound(removed_bound));

  EXPECT_THAT(empty_bounds_.nq_bounds(), ::testing::Not(::testing::Contains(removed_bound)));
}

TEST_F(TestBoundVector, Stdout) { EXPECT_NO_THROW(std::cout << bounds_ << std::endl); }