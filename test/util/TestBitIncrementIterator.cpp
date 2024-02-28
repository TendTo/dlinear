/**
 * @file TestBitIncrementIterator.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <stdexcept>

#include "dlinear/util/BitIncrementIterator.h"

using dlinear::BitIncrementIterator;

namespace {
std::vector<bool> number_to_bit_vector(size_t number, size_t dim) {
  std::vector<bool> result(dim, false);
  while (number > 0) {
    result[--dim] = number & 1;
    number >>= 1;
  }
  return result;
}
}  // namespace

TEST(TestBitIncrementIterator, PositiveNumberInitialisation) {
  const size_t dim = 6u;
  BitIncrementIterator it{dim};
  EXPECT_TRUE(it);
  EXPECT_EQ(it->size(), dim);
  EXPECT_EQ((*it).size(), dim);
  EXPECT_THAT(*it, ::testing::Each(::testing::AllOf(::testing::Eq(false))));
}

TEST(TestBitIncrementIterator, ZeroInitialisation) {
  const size_t dim = 0u;
  BitIncrementIterator it{dim};
  EXPECT_FALSE(it);
  EXPECT_EQ(it->size(), dim);
  EXPECT_EQ((*it).size(), dim);
}

TEST(TestBitIncrementIterator, ValidIncrement) {
  const size_t dim = 6u;
  BitIncrementIterator it{dim};
  for (size_t counter = 0; it; ++it, ++counter) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
}

TEST(TestBitIncrementIterator, ZeroInvalidIncrement) {
  const size_t dim = 0;
  BitIncrementIterator it{dim};
  EXPECT_NO_THROW(++it);
  EXPECT_FALSE(it);
  EXPECT_EQ(it->size(), dim);
}

TEST(TestBitIncrementIterator, InvalidIncrement) {
  const size_t dim = 6u;
  BitIncrementIterator it{dim};
  while (++it) {
  }
  EXPECT_NO_THROW(++it);
  EXPECT_FALSE(it);
  EXPECT_NE(it->size(), dim);
  EXPECT_EQ(it->size(), 0u);
}

TEST(TestBitIncrementIterator, LearnFirstElement) {
  const size_t dim = 5u;
  BitIncrementIterator it{dim};
  it.Learn(0);
  for (size_t counter = 1 << (dim - 1); it; ++it, ++counter) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
}

TEST(TestBitIncrementIterator, LearnMiddleElement) {
  const size_t dim = 5u;
  const size_t mask = 1 << (dim - 3);
  BitIncrementIterator it{dim};
  it.Learn(2);
  for (size_t counter = mask; it; ++it, ++counter, counter |= mask) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
}

TEST(TestBitIncrementIterator, LearnLastElement) {
  const size_t dim = 5u;
  const size_t mask = 1;
  BitIncrementIterator it{dim};
  it.Learn(dim - 1);
  for (size_t counter = mask; it; ++it, ++counter, counter |= mask) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
}

TEST(TestBitIncrementIterator, LearnResetPreviouosElements) {
  const size_t dim = 5u;
  const size_t mask = 1 << (dim - 2);
  BitIncrementIterator it{dim};
  for (; it; ++it) {
    if ((*it)[1]) break;
  }
  EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(mask, dim)));
  it.Learn(0);
  for (size_t counter = 1 << (dim - 1); it; ++it, ++counter) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
}

TEST(TestBitIncrementIterator, MultipleLearn) {
  const size_t dim = 5u;
  const size_t mask = 1 << (dim - 2) | 1 << (dim - 3);
  BitIncrementIterator it{dim};
  it.Learn(1);
  it.Learn(2);
  for (size_t counter = mask; it; ++it, ++counter, counter |= mask) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
}

TEST(TestBitIncrementIterator, LearnToFalse) {
  const size_t dim = 5u;
  const size_t mask = 1 << (dim - 2) | 1 << (dim - 3);
  BitIncrementIterator it{dim};
  it.Learn(1, false);
  it.Learn(2, false);
  for (size_t counter = 0; it; ++it, counter += mask, ++counter, counter &= ~mask) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
}
