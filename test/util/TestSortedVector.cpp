/**
 * @file TestSortedVector.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include "dlinear/util/SortedVector.hpp"

using dlinear::SortedVector;

class TestSortedVector : public ::testing::Test {
 protected:
  std::vector<int> v_{1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
  SortedVector<int> sv_{1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
  SortedVector<int> dv_{1, 2, 3, 4, 5, 5, 6, 7, 8, 9, 10};
  SortedVector<int> dsv_{1, 2, 3, 4, 5, 5, 6, 7, 8, 9, 10};
};

TEST_F(TestSortedVector, EmptyContructor) {
  SortedVector<int> sv;
  EXPECT_TRUE(sv.empty());
  EXPECT_EQ(sv.size(), 0u);
}

TEST_F(TestSortedVector, SizeConstructor) {
  SortedVector<int> sv(10);
  EXPECT_FALSE(sv.empty());
  EXPECT_EQ(sv.size(), 10u);
  EXPECT_THAT(sv, ::testing::Each(0));
}

TEST_F(TestSortedVector, SortedInitialisationListConstructor) {
  SortedVector<int> sv{1, 2, 3, 4, 5};
  EXPECT_FALSE(sv.empty());
  EXPECT_EQ(sv.size(), 5u);
  EXPECT_THAT(sv, ::testing::ElementsAre(1, 2, 3, 4, 5));
}

TEST_F(TestSortedVector, InitialisationListConstructor) {
  SortedVector<int> sv{5, 2, 4, 1, 3};
  EXPECT_FALSE(sv.empty());
  EXPECT_EQ(sv.size(), 5u);
  EXPECT_THAT(sv, ::testing::ElementsAre(1, 2, 3, 4, 5));
}

TEST_F(TestSortedVector, CopyConstructor) {
  SortedVector<int> sv{5, 2, 4, 1, 3};
  SortedVector<int> sv2{sv};
  EXPECT_FALSE(sv2.empty());
  EXPECT_EQ(sv2.size(), 5u);
  EXPECT_THAT(sv2, ::testing::ElementsAre(1, 2, 3, 4, 5));
}

TEST_F(TestSortedVector, MoveConstructor) {
  SortedVector<int> sv{5, 2, 4, 1, 3};
  SortedVector<int> sv2{std::move(sv)};
  EXPECT_FALSE(sv2.empty());
  EXPECT_EQ(sv2.size(), 5u);
  EXPECT_THAT(sv2, ::testing::ElementsAre(1, 2, 3, 4, 5));
  EXPECT_TRUE(sv.empty());
  EXPECT_EQ(sv.size(), 0u);
}

TEST_F(TestSortedVector, CopyAssignment) {
  SortedVector<int> sv{5, 2, 4, 1, 3};
  SortedVector<int> sv2;
  sv2 = sv;
  EXPECT_FALSE(sv2.empty());
  EXPECT_EQ(sv2.size(), 5u);
  EXPECT_THAT(sv2, ::testing::ElementsAre(1, 2, 3, 4, 5));
}

TEST_F(TestSortedVector, MoveAssignment) {
  SortedVector<int> sv{5, 2, 4, 1, 3};
  SortedVector<int> sv2;
  sv2 = std::move(sv);
  EXPECT_FALSE(sv2.empty());
  EXPECT_EQ(sv2.size(), 5u);
  EXPECT_THAT(sv2, ::testing::ElementsAre(1, 2, 3, 4, 5));
  EXPECT_TRUE(sv.empty());
  EXPECT_EQ(sv.size(), 0u);
}

TEST_F(TestSortedVector, CustomComparator) {
  SortedVector<int, std::greater<>> sv{5, 2, 4, 1, 3};
  EXPECT_THAT(sv, ::testing::ElementsAre(5, 4, 3, 2, 1));
}

TEST_F(TestSortedVector, Insert) {
  SortedVector<int> sv;
  const size_t dim = 5;
  const int elements[dim] = {5, 2, 4, 1, 3};
  for (size_t i = 0; i < dim; i++) {
    auto it = sv.insert(elements[i]);
    EXPECT_EQ(*it, elements[i]);
    EXPECT_FALSE(sv.empty());
    EXPECT_EQ(sv.size(), i + 1);
  }
  EXPECT_THAT(sv, ::testing::ElementsAre(1, 2, 3, 4, 5));
}

TEST_F(TestSortedVector, InsertDuplicate) {
  SortedVector<int> sv{5, 2, 4, 1, 3};
  auto it = sv.insert(5);
  EXPECT_THAT(sv, ::testing::ElementsAre(1, 2, 3, 4, 5, 5));
  EXPECT_EQ(it, sv.begin() + 4);
  it = sv.insert(3);
  EXPECT_THAT(sv, ::testing::ElementsAre(1, 2, 3, 3, 4, 5, 5));
  EXPECT_EQ(it, sv.begin() + 2);
  sv.insert(3);
  EXPECT_THAT(sv, ::testing::ElementsAre(1, 2, 3, 3, 3, 4, 5, 5));
  EXPECT_EQ(it, sv.begin() + 2);
}

TEST_F(TestSortedVector, Emplace) {
  SortedVector<int> sv;
  const size_t dim = 5;
  const int elements[dim] = {5, 2, 4, 1, 3};
  for (size_t i = 0; i < dim; i++) {
    sv.emplace(elements[i]);
    EXPECT_FALSE(sv.empty());
    EXPECT_EQ(sv.size(), i + 1);
  }
  EXPECT_THAT(sv, ::testing::ElementsAre(1, 2, 3, 4, 5));
}

TEST_F(TestSortedVector, At) {
  for (size_t i = 0; i < sv_.size(); i++) {
    EXPECT_EQ(sv_.at(i), static_cast<int>(i) + 1);
  }
}

TEST_F(TestSortedVector, SquareBrackets) {
  for (size_t i = 0; i < sv_.size(); i++) {
    EXPECT_EQ(sv_[i], static_cast<int>(i) + 1);
  }
}

TEST_F(TestSortedVector, AtNegative) {
  for (int i = -1; i >= -static_cast<int>(sv_.size()); i--) {
    EXPECT_EQ(sv_.at(i), static_cast<int>(sv_.size()) + i + 1);
  }
}

TEST_F(TestSortedVector, OutOfRangeAt) {
  EXPECT_THROW(sv_.at(sv_.size()), std::out_of_range);
  EXPECT_THROW(sv_.at(-sv_.size() - 1), std::out_of_range);
}

TEST_F(TestSortedVector, EraseElement) {
  SortedVector<int> sv{5, 2, 4, 1, 3};
  EXPECT_TRUE(sv.erase_value(3));
  EXPECT_THAT(sv, ::testing::ElementsAre(1, 2, 4, 5));
  EXPECT_TRUE(sv.erase_value(1));
  EXPECT_THAT(sv, ::testing::ElementsAre(2, 4, 5));
  EXPECT_TRUE(sv.erase_value(5));
  EXPECT_THAT(sv, ::testing::ElementsAre(2, 4));
}

TEST_F(TestSortedVector, EraseElementNonExistent) {
  EXPECT_FALSE(sv_.erase_value(11));
  EXPECT_THAT(sv_, ::testing::ElementsAreArray(v_));
}

TEST_F(TestSortedVector, EraseElementMultiple) {
  EXPECT_TRUE(dsv_.erase_value(5));
  EXPECT_THAT(dsv_, ::testing::ElementsAreArray(v_));
}

TEST_F(TestSortedVector, Erase) {
  SortedVector<int> sv{5, 2, 4, 1, 3};
  EXPECT_TRUE(sv.erase(3));
  EXPECT_THAT(sv, ::testing::ElementsAre(1, 2, 3, 5));
  EXPECT_TRUE(sv.erase(1));
  EXPECT_THAT(sv, ::testing::ElementsAre(1, 3, 5));
  EXPECT_TRUE(sv.erase(0));
  EXPECT_THAT(sv, ::testing::ElementsAre(3, 5));
}

TEST_F(TestSortedVector, EraseOutOfRange) {
  EXPECT_FALSE(sv_.erase(11));
  EXPECT_THAT(sv_, ::testing::ElementsAreArray(v_));
}

TEST_F(TestSortedVector, EraseMultiple) {
  EXPECT_TRUE(dsv_.erase(5));
  EXPECT_THAT(dsv_, ::testing::ElementsAreArray(v_));
  EXPECT_TRUE(dsv_.erase(5));
}

TEST_F(TestSortedVector, Find) {
  for (int i = 1; i <= 10; i++) {
    EXPECT_EQ(sv_.find(i), sv_.begin() + (i - 1));
  }
}
TEST_F(TestSortedVector, FindAbsent) { EXPECT_EQ(sv_.find(11), sv_.end()); }
TEST_F(TestSortedVector, FindMutiple) {
  EXPECT_EQ(dsv_.find(5), dsv_.begin() + 4);
  dsv_.erase_value(5);  // Erase one of the 5s
  EXPECT_EQ(dsv_.find(5), dsv_.begin() + 4);
}

TEST_F(TestSortedVector, CountSingle) { EXPECT_EQ(dsv_.count(1), 1u); }
TEST_F(TestSortedVector, ConuntAbsent) { EXPECT_EQ(dsv_.count(11), 0u); }
TEST_F(TestSortedVector, CountMutilple) {
  EXPECT_EQ(dsv_.count(5), 2u);
  dsv_.erase_value(5);  // Erase one of the 5s
  EXPECT_EQ(dsv_.count(5), 1u);
}

TEST_F(TestSortedVector, Contains) { EXPECT_TRUE(sv_.contains(1)); }
TEST_F(TestSortedVector, ContainsAbsent) { EXPECT_FALSE(dsv_.contains(11)); }
TEST_F(TestSortedVector, ContainsMultiple) {
  EXPECT_TRUE(dsv_.contains(5));
  dsv_.erase_value(5);  // Erase one of the 5s
  EXPECT_TRUE(dsv_.contains(5));
}

TEST_F(TestSortedVector, LowerBound) {
  for (int i = 1; i <= 10; i++) {
    EXPECT_EQ(sv_.lesser_end(i), sv_.begin() + (i - 1));
  }
}
TEST_F(TestSortedVector, LowerBoundMultiple) {
  EXPECT_EQ(dsv_.lesser_end(5), dsv_.begin() + 4);
  EXPECT_EQ(*((sv_.lesser_end(5)) - 1), 4);
}
TEST_F(TestSortedVector, LowerBoundOutOfRange) {
  EXPECT_EQ(sv_.lesser_end(11), sv_.end());
  EXPECT_EQ(sv_.lesser_end(0), sv_.begin());
}
TEST_F(TestSortedVector, LowerBoundAbsent) {
  sv_.erase_value(5);
  EXPECT_EQ(sv_.lesser_end(5), sv_.begin() + 4);
  EXPECT_EQ(*sv_.lesser_end(5), 6);
  EXPECT_EQ(*(sv_.lesser_end(5) - 1), 4);
}

TEST_F(TestSortedVector, UpperBound) {
  for (int i = 1; i <= 10; i++) {
    EXPECT_EQ(sv_.greater_begin(i), sv_.begin() + i);
  }
}
TEST_F(TestSortedVector, UpperBoundMultiple) {
  EXPECT_EQ(dsv_.greater_begin(5), dsv_.begin() + 6);
  EXPECT_EQ(*(sv_.greater_begin(5)), 6);
}
TEST_F(TestSortedVector, UpperBoundOutOfRange) {
  EXPECT_EQ(sv_.greater_begin(11), sv_.end());
  EXPECT_EQ(sv_.greater_begin(0), sv_.begin());
}
TEST_F(TestSortedVector, UpperBoundAbsent) {
  sv_.erase_value(5);
  EXPECT_EQ(sv_.greater_begin(5), sv_.begin() + 4);
  EXPECT_EQ(*sv_.greater_begin(5), 6);
}

TEST_F(TestSortedVector, Clear) {
  sv_.clear();
  EXPECT_TRUE(sv_.empty());
  EXPECT_EQ(sv_.size(), 0u);
}

TEST_F(TestSortedVector, Stdout) { EXPECT_NO_THROW(std::cout << sv_); }
