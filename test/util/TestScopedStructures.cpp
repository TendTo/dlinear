/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gtest/gtest.h>

#include <vector>

#include "dlinear/util/ScopedUnorderedMap.hpp"
#include "dlinear/util/ScopedUnorderedSet.hpp"
#include "dlinear/util/ScopedVector.hpp"

using dlinear::ScopedUnorderedMap;
using dlinear::ScopedUnorderedSet;
using dlinear::ScopedVector;
using std::vector;

// Push each element of vector<int> to scoped_vector<int> and check if
// the two have the same elements.
TEST(TestScopedVector, PushBack) {
  const vector<int> vec{1, 2, 3, 4, 5, 6, 7, 8, 9, 10};

  ScopedVector<int> scoped_vector{};
  for (const auto &item : vec) {
    scoped_vector.push_back(item);
  }

  EXPECT_EQ(vec, scoped_vector.get_vector());
}

TEST(TestScopedVector, Push) {
  ScopedVector<int> scoped_vector{};

  scoped_vector.push_back(1);
  scoped_vector.push_back(2);
  scoped_vector.push_back(3);

  // First push.
  scoped_vector.push();

  scoped_vector.push_back(4);
  scoped_vector.push_back(5);
  scoped_vector.push_back(6);

  // Second push.
  scoped_vector.push();

  // Third push. Note that there is no push_back operation between 2nd
  // and 3rd pushes.
  scoped_vector.push();

  scoped_vector.push_back(7);
  scoped_vector.push_back(8);
  scoped_vector.push_back(9);

  // It should include {1,2,3,4,5,6,7,8,9}.
  EXPECT_EQ(scoped_vector.size(), 9U);
  EXPECT_EQ(scoped_vector.get_vector(), vector<int>({1, 2, 3, 4, 5, 6, 7, 8, 9}));

  // After pop, it should include {1,2,3,4,5,6}.
  scoped_vector.pop();
  EXPECT_EQ(scoped_vector.size(), 6U);
  EXPECT_EQ(scoped_vector.get_vector(), vector<int>({1, 2, 3, 4, 5, 6}));

  // After pop, it should still include {1,2,3,4,5,6}.
  scoped_vector.pop();
  EXPECT_EQ(scoped_vector.size(), 6U);
  EXPECT_EQ(scoped_vector.get_vector(), vector<int>({1, 2, 3, 4, 5, 6}));

  // After pop, it should include {1,2,3}.
  scoped_vector.pop();
  EXPECT_EQ(scoped_vector.size(), 3U);
  EXPECT_EQ(scoped_vector.get_vector(), vector<int>({1, 2, 3}));

  // There should be nothing to pop and it throws runtime_error.
  EXPECT_THROW(scoped_vector.pop(), std::runtime_error);
}

GTEST_TEST(ScopedUnorderedMapTest, CopyConstruct) {
  ScopedUnorderedMap<int, int> map1;
  map1.insert(1, 2);
  map1.insert(2, 3);
  map1.insert(3, 4);

  const ScopedUnorderedMap<int, int> map2(map1);
  EXPECT_EQ(map1.size(), map2.size());
  for (const auto &p : map1) {
    const int &k = p.first;
    EXPECT_EQ(map1[k], map2[k]);
  }
}

GTEST_TEST(ScopedUnorderedMapTest, MoveConstruct) {
  ScopedUnorderedMap<int, int> map1;
  map1.insert(1, 2);
  map1.insert(2, 3);
  map1.insert(3, 4);

  const ScopedUnorderedMap<int, int> map2(std::move(map1));
  EXPECT_EQ(map2.size(), 3u);
  EXPECT_EQ(map2[1], 2);
  EXPECT_EQ(map2[2], 3);
  EXPECT_EQ(map2[3], 4);
}

GTEST_TEST(ScopedUnorderedMapTest, CopyOp) {
  ScopedUnorderedMap<int, int> map1;
  map1.insert(1, 2);
  map1.insert(2, 3);
  map1.insert(3, 4);

  ScopedUnorderedMap<int, int> map2;
  map2 = map1;
  EXPECT_EQ(map1.size(), map2.size());
  for (const auto &p : map1) {
    const int &k = p.first;
    EXPECT_EQ(map1[k], map2[k]);
  }
}

GTEST_TEST(ScopedUnorderedMapTest, MoveOp) {
  ScopedUnorderedMap<int, int> map1;
  map1.insert(1, 2);
  map1.insert(2, 3);
  map1.insert(3, 4);

  ScopedUnorderedMap<int, int> map2;
  map2 = std::move(map1);
  EXPECT_EQ(map2.size(), 3u);
  EXPECT_EQ(map2[1], 2);
  EXPECT_EQ(map2[2], 3);
  EXPECT_EQ(map2[3], 4);
}

GTEST_TEST(ScopedUnorderedMapTest, Clear) {
  ScopedUnorderedMap<int, int> map1;
  map1.insert(1, 2);
  map1.push();
  map1.insert(2, 3);
  map1.insert(3, 4);
  EXPECT_EQ(map1.size(), 3u);

  map1.clear();
  EXPECT_EQ(map1.size(), 0u);

  EXPECT_THROW(map1.pop(), std::runtime_error);
}

GTEST_TEST(ScopedUnorderedMapTest, Update) {
  ScopedUnorderedMap<int, int> map;
  map.insert(1, 2);
  EXPECT_EQ(map[1], 2);
  EXPECT_EQ(map.size(), 1u);

  map.insert(1, 3);  // Update
  EXPECT_EQ(map[1], 3);
  EXPECT_EQ(map.size(), 1u);

  EXPECT_THROW(map[2], std::runtime_error);
}

GTEST_TEST(ScopedUnorderedMapTest, PushPop) {
  ScopedUnorderedMap<int, int> map;
  EXPECT_TRUE(map.empty());

  map.push();

  map.insert(1, 2);
  EXPECT_EQ(map[1], 2);
  EXPECT_EQ(map.size(), 1u);
  EXPECT_FALSE(map.empty());

  map.push();

  map.insert(1, 3);  // Update
  map.insert(2, 4);
  EXPECT_EQ(map.size(), 2u);
  EXPECT_EQ(map[1], 3);
  EXPECT_EQ(map[2], 4);
  EXPECT_FALSE(map.empty());

  map.pop();

  EXPECT_EQ(map.size(), 1u);
  EXPECT_EQ(map[1], 2);         // Old value should be restored.
  EXPECT_EQ(map.count(2), 0u);  // the entry for '2' is deleted.
  EXPECT_FALSE(map.empty());

  map.pop();
  EXPECT_TRUE(map.empty());
}

GTEST_TEST(ScopedUnorderedSetTest, CopyConstruct) {
  ScopedUnorderedSet<int> set1;
  set1.insert(1);
  set1.insert(2);
  set1.insert(3);

  const ScopedUnorderedSet<int> set2(set1);
  EXPECT_EQ(set1.size(), set2.size());
  for (const auto &k : set1) {
    EXPECT_EQ(set2.count(k), 1u);
  }
}

GTEST_TEST(ScopedUnorderedSetTest, MoveConstruct) {
  ScopedUnorderedSet<int> set1;
  set1.insert(1);
  set1.insert(2);
  set1.insert(3);

  const ScopedUnorderedSet<int> set2(std::move(set1));
  EXPECT_EQ(set2.size(), 3u);
  EXPECT_EQ(set2.count(1), 1u);
  EXPECT_EQ(set2.count(2), 1u);
  EXPECT_EQ(set2.count(3), 1u);
}

GTEST_TEST(ScopedUnorderedSetTest, CopyOp) {
  ScopedUnorderedSet<int> set1;
  set1.insert(1);
  set1.insert(2);
  set1.insert(3);

  ScopedUnorderedSet<int> set2;
  set2 = set1;
  EXPECT_EQ(set1.size(), set2.size());
  for (const auto &k : set1) {
    EXPECT_EQ(set2.count(k), 1u);
  }
}

GTEST_TEST(ScopedUnorderedSetTest, MoveOp) {
  ScopedUnorderedSet<int> set1;
  set1.insert(1);
  set1.insert(2);
  set1.insert(3);

  ScopedUnorderedSet<int> set2;
  set2 = std::move(set1);
  EXPECT_EQ(set2.size(), 3u);
  EXPECT_EQ(set2.count(1), 1u);
  EXPECT_EQ(set2.count(2), 1u);
  EXPECT_EQ(set2.count(3), 1u);
}

GTEST_TEST(ScopedUnorderedSetTest, Clear) {
  ScopedUnorderedSet<int> set1;
  set1.insert(1);
  set1.push();
  set1.insert(2);
  set1.insert(3);
  EXPECT_EQ(set1.size(), 3u);

  set1.clear();
  EXPECT_EQ(set1.size(), 0u);

  EXPECT_THROW(set1.pop(), std::runtime_error);
}

GTEST_TEST(ScopedUnorderedSetTest, PushPop) {
  ScopedUnorderedSet<int> set;
  EXPECT_TRUE(set.empty());

  set.push();

  set.insert(1);
  EXPECT_EQ(set.count(1), 1u);
  EXPECT_EQ(set.size(), 1u);
  EXPECT_FALSE(set.empty());

  set.push();

  set.insert(1);  // No op
  set.insert(2);
  EXPECT_EQ(set.size(), 2u);
  EXPECT_EQ(set.count(1), 1u);
  EXPECT_EQ(set.count(2), 1u);
  EXPECT_FALSE(set.empty());

  set.pop();
  EXPECT_EQ(set.size(), 1u);
  EXPECT_EQ(set.count(1), 1u);
  EXPECT_EQ(set.count(2), 0u);  // the entry for '2' is deleted.
  EXPECT_FALSE(set.empty());

  set.pop();
  EXPECT_TRUE(set.empty());
}