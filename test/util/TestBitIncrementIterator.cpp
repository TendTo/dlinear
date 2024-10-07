/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
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

size_t bit_vector_to_number(const std::vector<bool>& vector) {
  size_t result = 0;
  for (const bool bit : vector) {
    result <<= 1;
    result |= bit;
  }
  return result;
}

std::vector<std::vector<bool>> enumerate_bit_vectors(const size_t dim) {
  std::vector<std::vector<bool>> result;
  for (BitIncrementIterator it{dim}; it; ++it) {
    result.push_back(*it);
  }
  return result;
}

std::vector<size_t> get_indexes(const size_t dim) {
  std::vector<size_t> result;
  for (size_t i = 0; i < dim; ++i) {
    result.push_back(i);
  }
  return result;
}

std::vector<size_t> get_start(const size_t dim) {
  std::vector<size_t> result;
  for (size_t i = 0; i < 1u << (dim - 1); ++i) {
    result.push_back(i);
  }
  return result;
}

}  // namespace

const size_t TEST_VECTOR_DIM = 5;

class TestBitIncrementIteratorBegin : public ::testing::TestWithParam<std::tuple<std::vector<bool>, size_t>> {};
class TestBitIncrementIteratorAdvanced
    : public ::testing::TestWithParam<std::tuple<std::vector<bool>, size_t, size_t>> {};

INSTANTIATE_TEST_SUITE_P(TestBitIncrementIterator, TestBitIncrementIteratorBegin,
                         ::testing::Combine(::testing::ValuesIn(enumerate_bit_vectors(TEST_VECTOR_DIM)),
                                            ::testing::ValuesIn(get_indexes(TEST_VECTOR_DIM))));

INSTANTIATE_TEST_SUITE_P(TestBitIncrementIterator, TestBitIncrementIteratorAdvanced,
                         ::testing::Combine(::testing::ValuesIn(enumerate_bit_vectors(TEST_VECTOR_DIM)),
                                            ::testing::ValuesIn(get_indexes(TEST_VECTOR_DIM)),
                                            ::testing::ValuesIn(get_start(TEST_VECTOR_DIM))));

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

TEST(TestBitIncrementIterator, VectorInitialisation) {
  const size_t dim = 4u;
  const std::vector<bool> start{true, false, true, false};
  EXPECT_EQ(start.size(), dim);
  BitIncrementIterator it{start};
  EXPECT_TRUE(it);
  EXPECT_EQ(it->size(), dim);
  EXPECT_EQ((*it).size(), dim);
  EXPECT_THAT(*it, ::testing::ElementsAreArray(start));
}

TEST(TestBitIncrementIterator, ValidIncrement) {
  const size_t dim = 6u;
  BitIncrementIterator it{dim};
  size_t counter = 0;
  for (; it; ++it, ++counter) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
  EXPECT_EQ(counter, 1u << dim);
}

TEST(TestBitIncrementIterator, VectorValidIncrement) {
  const size_t dim = 5u;
  const size_t mask = (1 << dim) - 1;
  const std::vector<bool> start{true, false, true, false, false};
  EXPECT_EQ(start.size(), dim);
  size_t iterations = 0;
  BitIncrementIterator it{start};
  for (size_t counter = 0b10100; it; ++it, counter = (counter + 1) & mask, ++iterations) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
  EXPECT_EQ(iterations, 1u << dim);
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
  size_t iterations = 0;
  BitIncrementIterator it{dim};
  it.Learn(0);
  for (size_t counter = 1 << (dim - 1); it; ++it, ++counter, ++iterations) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
  EXPECT_EQ(iterations, 1u << (dim - 1));
}

TEST(TestBitIncrementIterator, LearnMiddleElement) {
  const size_t dim = 5u;
  const size_t mask = 1 << (dim - 3);
  size_t iterations = 0;
  BitIncrementIterator it{dim};
  it.Learn(2);
  for (size_t counter = mask; it; ++it, ++counter, counter |= mask, ++iterations) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
  EXPECT_EQ(iterations, 1u << (dim - 1));
}

TEST(TestBitIncrementIterator, LearnLastElement) {
  const size_t dim = 5u;
  const size_t mask = 1;
  size_t iterations = 0;
  BitIncrementIterator it{dim};
  it.Learn(dim - 1);
  for (size_t counter = mask; it; ++it, ++counter, counter |= mask, ++iterations) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
  EXPECT_EQ(iterations, 1u << (dim - 1));
}

TEST(TestBitIncrementIterator, MultipleLearn) {
  const size_t dim = 5u;
  const size_t mask = 1 << (dim - 2) | 1 << (dim - 3);
  size_t iterations = 0;
  BitIncrementIterator it{dim};
  it.Learn(1);
  it.Learn(2);
  for (size_t counter = mask; it; ++it, ++counter, counter |= mask, ++iterations) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
  EXPECT_EQ(iterations, 1u << (dim - 2));
}

TEST(TestBitIncrementIterator, MultipleLearnToFalse) {
  const size_t dim = 5u;
  const size_t mask = 1 << (dim - 2) | 1 << (dim - 3);
  size_t iterations = 0;
  BitIncrementIterator it{dim};
  it.Learn(1, false);
  it.Learn(2, false);
  for (size_t counter = 0; it; ++it, counter += mask, ++counter, counter &= ~mask, ++iterations) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
  EXPECT_EQ(iterations, 1u << (dim - 2));
}

TEST(TestBitIncrementIterator, LearnTrueResetPreviouosElements) {
  const size_t dim = 5u;
  const size_t mask = 1 << (dim - 2);
  size_t iterations = 0;
  BitIncrementIterator it{dim};
  for (; it; ++it, ++iterations) {
    if ((*it)[1]) break;
  }
  EXPECT_EQ(iterations, 1u << (dim - 2));
  EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(mask, dim)));
  it.Learn(0);
  for (size_t counter = 1 << (dim - 1); it; ++it, ++counter, ++iterations) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
  EXPECT_EQ(iterations, (1u << (dim - 2)) + (1u << (dim - 1)));
}

TEST(TestBitIncrementIterator, LearnFalseResetPreviouosElements) {
  const size_t dim = 5u;
  const size_t mask = 1 << (dim - 2);
  size_t iterations = 0;
  BitIncrementIterator it{dim};
  for (; it; ++it, ++iterations) {
    if ((*it)[1]) break;
  }
  EXPECT_EQ(iterations, 1u << (dim - 2));
  EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(mask, dim)));
  it.Learn(0);
  for (size_t counter = 1 << (dim - 1); it; ++it, ++counter, ++iterations) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
  EXPECT_EQ(iterations, (1u << (dim - 2)) + (1u << (dim - 1)));
}

TEST(TestBitIncrementIterator, LearnTrueAdvancedVectorInit) {
  const size_t dim = 4u;
  size_t iterations = 0;
  BitIncrementIterator it{{false, false, true, true}};
  for (; iterations < 2; ++iterations) ++it;
  EXPECT_FALSE((*it)[0]);
  it.Learn(0);
  for (size_t counter = 1 << (dim - 1) | 0b0011; it;
       ++it, ++counter, counter |= 0b1000, counter &= 0b1111, ++iterations) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
  EXPECT_EQ(iterations, 2 + (1u << (dim - 1)));
}

TEST(TestBitIncrementIterator, FirstBitTrue) {
  const size_t dim = 4u;
  size_t iterations = 0;
  BitIncrementIterator it{{true, false, false, false}};
  it.Learn(0);
  EXPECT_FALSE((*it)[0]);
  for (size_t counter = 0b0000; it; ++it, ++counter, ++iterations) {
    EXPECT_EQ(it->size(), dim);
    EXPECT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
  EXPECT_EQ(iterations, (1u << (dim - 1)));
}

TEST(TestBitIncrementIterator, DoubleLearn) {
  size_t iterations = 0;
  BitIncrementIterator it{19};
  it.Learn(13);
  it.Learn(16);
  EXPECT_TRUE((*it)[13]);
  EXPECT_TRUE((*it)[16]);
  for (const bool val : *it) {
    if (iterations == 13 || iterations == 16) continue;
    EXPECT_FALSE(val);
    iterations++;
  }
}

TEST_P(TestBitIncrementIteratorBegin, LearnTrueVectorInit) {
  const auto& [start_value, idx] = GetParam();
  // Only handle "learn true" cases
  if (start_value[idx]) return;
  const size_t dim = start_value.size();
  const size_t mask = (1 << dim) - 1;
  const size_t fixed = 1 << (dim - 1 - idx);
  size_t iterations = 0;
  BitIncrementIterator it{{start_value}};
  it.Learn(idx);
  for (size_t counter = bit_vector_to_number(*it); it;
       ++it, ++counter, counter |= fixed, counter &= mask, ++iterations) {
    ASSERT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
  EXPECT_EQ(iterations, (1u << (dim - 1)));
}

TEST_P(TestBitIncrementIteratorBegin, LearnFalseVectorInit) {
  const auto& [start_value, idx] = GetParam();
  // Only handle "learn false" cases
  if (!start_value[idx]) return;
  const size_t dim = start_value.size();
  const size_t fixed = (1 << (dim - 1 - idx));
  const size_t mask = ((1 << dim) - 1) & ~fixed;
  size_t iterations = 0;
  BitIncrementIterator it{{start_value}};
  it.Learn(idx);
  for (size_t counter = bit_vector_to_number(*it); it; ++it, counter += fixed + 1, counter &= mask, ++iterations) {
    ASSERT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
  EXPECT_EQ(iterations, (1u << (dim - 1)));
}

TEST_P(TestBitIncrementIteratorAdvanced, LearnTrueVectorInit) {
  const auto& [start_value, idx, initial_iterations] = GetParam();
  const size_t dim = start_value.size();
  const size_t mask = (1 << dim) - 1;
  const size_t fixed = 1 << (dim - 1 - idx);
  size_t iterations = 0;
  BitIncrementIterator it{{start_value}};
  for (size_t i = 0; i < initial_iterations; ++i, ++it) {
    if ((*it)[idx]) iterations++;
  }
  // Only handle "learn true" cases
  if ((*it)[idx]) return;
  it.Learn(idx);
  for (size_t counter = bit_vector_to_number(*it); it;
       ++it, ++counter, counter |= fixed, counter &= mask, ++iterations) {
    ASSERT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
  EXPECT_GE(iterations, (1u << (dim - 1)));
}

TEST_P(TestBitIncrementIteratorAdvanced, LearnFalseVectorInit) {
  const auto& [start_value, idx, initial_iterations] = GetParam();
  const size_t dim = start_value.size();
  const size_t fixed = (1 << (dim - 1 - idx));
  const size_t mask = ((1 << dim) - 1) & ~fixed;
  size_t iterations = 0;
  BitIncrementIterator it{{start_value}};
  for (size_t i = 0; i < initial_iterations; ++i, ++it) {
    if (!(*it)[idx]) iterations++;
  }
  // Only handle "learn false" cases
  if (!(*it)[idx]) return;
  it.Learn(idx);
  for (size_t counter = bit_vector_to_number(*it); it; ++it, counter += fixed + 1, counter &= mask, ++iterations) {
    ASSERT_THAT(*it, ::testing::ElementsAreArray(number_to_bit_vector(counter, dim)));
  }
  EXPECT_GE(iterations, (1u << (dim - 1)));
}
