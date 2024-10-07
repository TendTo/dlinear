/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gtest/gtest.h>

#include "dlinear/solver/BoundIterator.h"

using dlinear::Bound;
using dlinear::BoundIterator;
using dlinear::Literal;
using dlinear::LpColBound;
using dlinear::Variable;

class TestBoundIterator : public ::testing::Test {
 protected:
  const Literal lit_{Variable{"lit", Variable::Type::BOOLEAN}, true};
  const std::vector<Bound> bound_vector_;
  const std::vector<Bound> nq_bound_vector_;
  BoundIterator it_;
  const mpq_class val_[6] = {0, 1, 2, 3, 4, 5};

  TestBoundIterator()
      : bound_vector_{{&val_[1], LpColBound::SL, lit_},
                      {&val_[2], LpColBound::L, lit_},
                      {&val_[3], LpColBound::U, lit_},
                      {&val_[4], LpColBound::SU, lit_}},
        nq_bound_vector_{{&val_[0], LpColBound::D, lit_}, {&val_[5], LpColBound::D, lit_}},
        it_{bound_vector_.begin(), bound_vector_.end(), nq_bound_vector_.begin(), nq_bound_vector_.end()} {}
};

TEST_F(TestBoundIterator, ConstructorDefault) {
  BoundIterator it{};
  EXPECT_FALSE(it);
  EXPECT_EQ(it.size(), 0u);
  EXPECT_TRUE(it.empty());
  EXPECT_EQ(it.bounds_size(), 0u);
  EXPECT_TRUE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds_size(), 0u);
  EXPECT_TRUE(it.nq_bounds_empty());
}

TEST_F(TestBoundIterator, ConstructorSingleEmpty) {
  std::vector<Bound> empty_vector;
  BoundIterator it{empty_vector.begin(), empty_vector.end()};
  EXPECT_FALSE(it);
  EXPECT_EQ(it.size(), 0u);
  EXPECT_TRUE(it.empty());
  EXPECT_EQ(it.bounds_size(), 0u);
  EXPECT_TRUE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds_size(), 0u);
  EXPECT_TRUE(it.nq_bounds_empty());
}

TEST_F(TestBoundIterator, ConstructorDoubleEmpty) {
  std::vector<Bound> empty_vector;
  std::vector<Bound> empty_vector2;
  BoundIterator it{empty_vector.begin(), empty_vector.end(), empty_vector2.begin(), empty_vector2.end()};
  EXPECT_FALSE(it);
  EXPECT_EQ(it.size(), 0u);
  EXPECT_TRUE(it.empty());
  EXPECT_EQ(it.bounds_size(), 0u);
  EXPECT_TRUE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds_size(), 0u);
  EXPECT_TRUE(it.nq_bounds_empty());
}

TEST_F(TestBoundIterator, ConstructorSingle) {
  BoundIterator it{bound_vector_.begin(), bound_vector_.end()};
  EXPECT_TRUE(it);
  EXPECT_EQ(*it, bound_vector_[0]);
  EXPECT_EQ(it.size(), bound_vector_.size());
  EXPECT_FALSE(it.empty());
  EXPECT_EQ(it.bounds_size(), bound_vector_.size());
  EXPECT_FALSE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds_size(), 0u);
  EXPECT_TRUE(it.nq_bounds_empty());
  for (size_t i = 0; i < bound_vector_.size(); ++i) {
    EXPECT_EQ(it[i], bound_vector_[i]);
  }
}

TEST_F(TestBoundIterator, ConstructorDouble) {
  BoundIterator it{bound_vector_.begin(), bound_vector_.end(), nq_bound_vector_.begin(), nq_bound_vector_.end()};
  EXPECT_TRUE(it);
  EXPECT_EQ(*it, bound_vector_[0]);
  EXPECT_EQ(it.size(), bound_vector_.size() + nq_bound_vector_.size());
  EXPECT_FALSE(it.empty());
  EXPECT_EQ(it.bounds_size(), bound_vector_.size());
  EXPECT_FALSE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds_size(), nq_bound_vector_.size());
  EXPECT_FALSE(it.nq_bounds_empty());
  for (size_t i = 0; i < bound_vector_.size(); ++i) {
    EXPECT_EQ(it[i], bound_vector_[i]);
  }
  for (size_t i = 0; i < nq_bound_vector_.size(); ++i) {
    EXPECT_EQ(it[i + bound_vector_.size()], nq_bound_vector_[i]);
  }
}

TEST_F(TestBoundIterator, SingleIteration) {
  BoundIterator it{bound_vector_.begin(), bound_vector_.end()};
  EXPECT_TRUE(it);
  size_t i = 0;
  for (; it; ++it, ++i) {
    EXPECT_EQ(*it, bound_vector_[i]);
  }
  EXPECT_FALSE(it);
  EXPECT_EQ(i, bound_vector_.size());
}

TEST_F(TestBoundIterator, DoubleIteration) {
  EXPECT_TRUE(it_);
  size_t i = 0;
  for (; it_; ++it_, ++i) {
    if (i < bound_vector_.size()) {
      EXPECT_EQ(*it_, bound_vector_[i]);
    } else {
      EXPECT_EQ(*it_, nq_bound_vector_[i - bound_vector_.size()]);
    }
  }
  EXPECT_FALSE(it_);
  EXPECT_EQ(i, bound_vector_.size() + nq_bound_vector_.size());
}
