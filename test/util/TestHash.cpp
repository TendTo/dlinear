/**
 * @file TestHash.cpp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 */
#include <gtest/gtest.h>

#include <algorithm>

#include "dlinear/util/hash.hpp"

using dlinear::hash;
using dlinear::hash_combine;
using dlinear::hash_range;

TEST(TestHash, HashInt) {
  const size_t input{1};
  auto h = hash<size_t>(input);
  EXPECT_EQ(h, std::hash<size_t>{}(input));
}

TEST(TestHash, HashCombineSingle) {
  const size_t input{1};
  auto h = hash_combine(0, input);
  EXPECT_EQ(h, hash(input) + 0x9e3779b9);
}

TEST(TestHash, HashCombineSingleSeed) {
  const size_t seed{10}, input{1};
  auto h = hash_combine(seed, input);
  EXPECT_EQ(h, seed ^ (hash(input) + 0x9e3779b9 + (seed << 6) + (seed >> 2)));
}

TEST(TestHash, HashRange) {
  const std::vector<size_t> input{1, 2};
  auto h = hash_range(input.begin(), input.end());
  EXPECT_EQ(h, hash_combine(0, input[0], input[1]));
}

TEST(TestHash, HashRangeLong) {
  const std::vector<size_t> input{1, 2, 3, 4, 5, 6, 7, 8, 9};
  auto h = hash_range(input.begin(), input.end());
  EXPECT_EQ(h, hash_combine(0, input[0], input[1], input[2], input[3], input[4],
                            input[5], input[6], input[7], input[8]));
}

TEST(TestHash, HashCombineMultiple) {
  const size_t input1{1}, input2{2};
  auto h = hash_combine(0, input1, input2);
  EXPECT_EQ(h, hash_combine(hash_combine(0, input1), input2));
}

TEST(TestHash, HashPair) {
  const std::pair<size_t, size_t> input{1, 2};
  auto h = hash(input);
  EXPECT_EQ(h, hash_combine(0, input.first, input.second));
}

TEST(TestHash, HashVector) {
  const std::vector<size_t> input{1, 2};
  auto h = hash(input);
  EXPECT_EQ(h, hash_combine(0, input[0], input[1]));
}

TEST(TestHash, HashSet) {
  const std::set<size_t> input{1, 2};
  auto h = hash(input);
  EXPECT_EQ(h, hash_range(input.begin(), input.end()));
}

TEST(TestHash, HashMap) {
  const std::map<size_t, size_t> input{{1, 2}, {3, 4}};
  auto h = hash(input);
  EXPECT_EQ(h, hash_range(input.begin(), input.end()));
}
