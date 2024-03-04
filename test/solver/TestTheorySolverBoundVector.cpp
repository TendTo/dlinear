/**
 * @file TestTheorySolverBoundsVector.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "dlinear/solver/TheorySolverBoundVector.h"

using dlinear::TheorySolverBoundVector;

class TestSortedVector : public ::testing::Test {
 protected:
  std::vector<int> v_{1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
};

TEST_F(TestSortedVector, Constructor) {
  TheorySolverBoundVector bounds;
  EXPECT_EQ(bounds.n_less_than(), 0);
  EXPECT_EQ(bounds.n_greater_than(), 0);
  EXPECT_EQ(bounds.bounds().size(), 0u);
}
