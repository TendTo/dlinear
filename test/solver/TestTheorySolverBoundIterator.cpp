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
using dlinear::ViolationIterator;
using BoundVector = dlinear::TheorySolverBoundVector::BoundVector;

class TestTheorySolverBoundIterator : public ::testing::Test {
 protected:
  const BoundVector bound_vector_;
  const BoundVector nq_bound_vector_;
  ViolationIterator it_;

  TestTheorySolverBoundIterator()
      : bound_vector_{{1, LpColBound::SL, 0}, {2, LpColBound::L, 0}, {3, LpColBound::U, 0}, {4, LpColBound::SU, 0}},
        nq_bound_vector_{{0, LpColBound::D, 0}, {5, LpColBound::D, 0}},
        it_{bound_vector_.begin(), bound_vector_.end(), nq_bound_vector_.begin(), nq_bound_vector_.end()} {}
};

TEST_F(TestTheorySolverBoundIterator, ConstructorSingle) {
  ViolationIterator it{bound_vector_.begin(), bound_vector_.end()};
  EXPECT_TRUE(it);
  EXPECT_EQ(*it, bound_vector_[0]);
  EXPECT_EQ(it.size(), bound_vector_.size());
  for (size_t i = 0; i < bound_vector_.size(); ++i) {
    EXPECT_EQ(it[i], bound_vector_[i]);
  }
}

TEST_F(TestTheorySolverBoundIterator, ConstructorDouble) {
  ViolationIterator it{bound_vector_.begin(), bound_vector_.end(), nq_bound_vector_.begin(), nq_bound_vector_.end()};
  EXPECT_TRUE(it);
  EXPECT_EQ(*it, bound_vector_[0]);
  EXPECT_EQ(it.size(), bound_vector_.size() + nq_bound_vector_.size());
  for (size_t i = 0; i < bound_vector_.size(); ++i) {
    EXPECT_EQ(it[i], bound_vector_[i]);
  }
  for (size_t i = 0; i < nq_bound_vector_.size(); ++i) {
    EXPECT_EQ(it[i + bound_vector_.size()], nq_bound_vector_[i]);
  }
}

TEST_F(TestTheorySolverBoundIterator, SingleIteration) {
  ViolationIterator it{bound_vector_.begin(), bound_vector_.end()};
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
