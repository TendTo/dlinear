/**
 * @file TestTheorySolverBoundsVector.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include "dlinear/solver/TheorySolverBoundIterator.h"
#include "dlinear/solver/TheorySolverBoundVector.h"

using dlinear::LpColBound;
using dlinear::SortedVector;
using Violation = dlinear::TheorySolverBoundVector::BoundIterator;
using BoundVector = dlinear::TheorySolverBoundVector::BoundVector;

class TestTheorySolverBoundIterator : public ::testing::Test {
 protected:
  const BoundVector bound_vector_;
  const BoundVector nq_bound_vector_;
  Violation it_;

  TestTheorySolverBoundIterator()
      : bound_vector_{{1, LpColBound::SL, 0}, {2, LpColBound::L, 0}, {3, LpColBound::U, 0}, {4, LpColBound::SU, 0}},
        nq_bound_vector_{{0, LpColBound::D, 0}, {5, LpColBound::D, 0}},
        it_{bound_vector_.begin(), bound_vector_.end(), nq_bound_vector_.begin(), nq_bound_vector_.end()} {}
};

TEST_F(TestTheorySolverBoundIterator, ConstructorDefault) {
  Violation it{};
  EXPECT_FALSE(it);
  EXPECT_EQ(it.size(), 0u);
  EXPECT_TRUE(it.empty());
  EXPECT_EQ(it.bounds_size(), 0u);
  EXPECT_TRUE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds_size(), 0u);
  EXPECT_TRUE(it.nq_bounds_empty());
}

TEST_F(TestTheorySolverBoundIterator, ConstructorSingleEmpty) {
  BoundVector empty_vector;
  Violation it{empty_vector.begin(), empty_vector.end()};
  EXPECT_FALSE(it);
  EXPECT_EQ(it.size(), 0u);
  EXPECT_TRUE(it.empty());
  EXPECT_EQ(it.bounds_size(), 0u);
  EXPECT_TRUE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds_size(), 0u);
  EXPECT_TRUE(it.nq_bounds_empty());
}

TEST_F(TestTheorySolverBoundIterator, ConstructorDoubleEmpty) {
  BoundVector empty_vector;
  BoundVector empty_vector2;
  Violation it{empty_vector.begin(), empty_vector.end(), empty_vector2.begin(), empty_vector2.end()};
  EXPECT_FALSE(it);
  EXPECT_EQ(it.size(), 0u);
  EXPECT_TRUE(it.empty());
  EXPECT_EQ(it.bounds_size(), 0u);
  EXPECT_TRUE(it.bounds_empty());
  EXPECT_EQ(it.nq_bounds_size(), 0u);
  EXPECT_TRUE(it.nq_bounds_empty());
}

TEST_F(TestTheorySolverBoundIterator, ConstructorSingle) {
  Violation it{bound_vector_.begin(), bound_vector_.end()};
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

TEST_F(TestTheorySolverBoundIterator, ConstructorDouble) {
  Violation it{bound_vector_.begin(), bound_vector_.end(), nq_bound_vector_.begin(), nq_bound_vector_.end()};
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

TEST_F(TestTheorySolverBoundIterator, SingleIteration) {
  Violation it{bound_vector_.begin(), bound_vector_.end()};
  EXPECT_TRUE(it);
  size_t i = 0;
  for (; it; ++it, ++i) {
    EXPECT_EQ(*it, bound_vector_[i]);
  }
  EXPECT_FALSE(it);
  EXPECT_EQ(i, bound_vector_.size());
}

TEST_F(TestTheorySolverBoundIterator, DoubleIteration) {
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
