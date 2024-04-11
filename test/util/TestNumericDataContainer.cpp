/**
 * @file TestNumericDataContainer.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include <string>

#include "dlinear/libs/libgmp.h"
#include "dlinear/util/NumericDataContainer.hpp"

using dlinear::NumericDataContainer;

#define TNumericDataContainer NumericDataContainer<TypeParam, std::string>

template <class T>
class TestNumericDataContainer : public ::testing::Test {
 protected:
  NumericDataContainer<T, std::string> num_container_;
};

using TestParams = ::testing::Types<int, float, double, mpq_class>;
TYPED_TEST_SUITE(TestNumericDataContainer, TestParams);

TYPED_TEST(TestNumericDataContainer, DefaultContructor) {
  const TNumericDataContainer num_container;
  EXPECT_EQ(num_container.numeric, TypeParam{});
  EXPECT_EQ(num_container.data, std::string{});
}

TYPED_TEST(TestNumericDataContainer, NumericConstructor) {
  const TNumericDataContainer num_container{TypeParam{1}};
  EXPECT_EQ(num_container.numeric, TypeParam{1});
  EXPECT_EQ(num_container.data, std::string{});
}

TYPED_TEST(TestNumericDataContainer, FullConstructor) {
  const TNumericDataContainer num_container{TypeParam{1}, "data"};
  EXPECT_EQ(num_container.numeric, TypeParam{1});
  EXPECT_EQ(num_container.data, "data");
}

TYPED_TEST(TestNumericDataContainer, CopyConstructor) {
  const TNumericDataContainer num_container{TypeParam{1}, "data"};
  const TNumericDataContainer num_container_copy{num_container};
  EXPECT_EQ(num_container_copy.numeric, TypeParam{1});
  EXPECT_EQ(num_container_copy.data, "data");
}

TYPED_TEST(TestNumericDataContainer, MoveConstructor) {
  TNumericDataContainer num_container{TypeParam{1}, "data"};
  const TNumericDataContainer num_container_move{std::move(num_container)};
  EXPECT_EQ(num_container_move.numeric, TypeParam{1});
  EXPECT_EQ(num_container_move.data, "data");
}

TYPED_TEST(TestNumericDataContainer, CopyAssignment) {
  const TNumericDataContainer num_container{TypeParam{1}, "data"};
  TNumericDataContainer num_container_copy;
  num_container_copy = num_container;
  EXPECT_EQ(num_container_copy.numeric, TypeParam{1});
  EXPECT_EQ(num_container_copy.data, "data");
}

TYPED_TEST(TestNumericDataContainer, MoveAssignment) {
  TNumericDataContainer num_container{TypeParam{1}, "data"};
  TNumericDataContainer num_container_move;
  num_container_move = std::move(num_container);
  EXPECT_EQ(num_container_move.numeric, TypeParam{1});
  EXPECT_EQ(num_container_move.data, "data");
}

TYPED_TEST(TestNumericDataContainer, AdditionNumber) {
  const TypeParam a{7}, b{2};
  TNumericDataContainer num_container{a, "data"};
  num_container += b;
  EXPECT_EQ(num_container.numeric, a + b);
  EXPECT_EQ(num_container.data, "data");
}
TYPED_TEST(TestNumericDataContainer, AdditionContainer) {
  const TypeParam a{7}, b{2};
  TNumericDataContainer num_container{a, "data"};
  num_container += TNumericDataContainer{b, "data2"};
  EXPECT_EQ(num_container.numeric, a + b);
  EXPECT_EQ(num_container.data, "data");
}

TYPED_TEST(TestNumericDataContainer, SubtractionNumber) {
  const TypeParam a{7}, b{2};
  TNumericDataContainer num_container{a, "data"};
  num_container -= b;
  EXPECT_EQ(num_container.numeric, a - b);
  EXPECT_EQ(num_container.data, "data");
}
TYPED_TEST(TestNumericDataContainer, SubtractionContainer) {
  const TypeParam a{7}, b{2};
  TNumericDataContainer num_container{a, "data"};
  num_container -= TNumericDataContainer{b, "data2"};
  EXPECT_EQ(num_container.numeric, a - b);
  EXPECT_EQ(num_container.data, "data");
}

TYPED_TEST(TestNumericDataContainer, MultiplicationNumber) {
  const TypeParam a{7}, b{2};
  TNumericDataContainer num_container{a, "data"};
  num_container *= b;
  EXPECT_EQ(num_container.numeric, a * b);
  EXPECT_EQ(num_container.data, "data");
}
TYPED_TEST(TestNumericDataContainer, MultiplicationContainer) {
  const TypeParam a{7}, b{2};
  TNumericDataContainer num_container{a, "data"};
  num_container *= TNumericDataContainer{b, "data2"};
  EXPECT_EQ(num_container.numeric, a * b);
  EXPECT_EQ(num_container.data, "data");
}

TYPED_TEST(TestNumericDataContainer, DivisionNumber) {
  const TypeParam a{7}, b{2};
  TNumericDataContainer num_container{a, "data"};
  num_container /= b;
  EXPECT_EQ(num_container.numeric, a / b);
  EXPECT_EQ(num_container.data, "data");
}
TYPED_TEST(TestNumericDataContainer, DivisionContainer) {
  const TypeParam a{7}, b{2};
  TNumericDataContainer num_container{a, "data"};
  num_container /= TNumericDataContainer{b, "data2"};
  EXPECT_EQ(num_container.numeric, a / b);
  EXPECT_EQ(num_container.data, "data");
}

TYPED_TEST(TestNumericDataContainer, Equality) {
  const TypeParam a{7};
  const TNumericDataContainer num_container{a, "data"};

  EXPECT_EQ(a, num_container);
  EXPECT_EQ(num_container, a);

  TNumericDataContainer num_container2{a, "data"};
  EXPECT_EQ(num_container, num_container2);
  EXPECT_TRUE(num_container.EqualTo(num_container2));

  TNumericDataContainer num_container4{a, "data2"};
  EXPECT_EQ(num_container, num_container4);
  EXPECT_FALSE(num_container.EqualTo(num_container4));
}

TYPED_TEST(TestNumericDataContainer, InEquality) {
  const TypeParam a{7}, b{2};
  const TNumericDataContainer num_container{a, "data"};

  EXPECT_NE(b, num_container);
  EXPECT_NE(num_container, b);

  TNumericDataContainer num_container2{b, "data"};
  EXPECT_NE(num_container, num_container2);
}

TYPED_TEST(TestNumericDataContainer, LessThan) {
  const TypeParam a{2}, b{7};
  TNumericDataContainer num_container{a, "data"};

  EXPECT_LT(num_container, b);
  EXPECT_LT(a - 1, num_container);

  TNumericDataContainer num_container2{b, "a"};
  TNumericDataContainer num_container3{b, "z"};
  EXPECT_LT(num_container, num_container2);
}

TYPED_TEST(TestNumericDataContainer, LessThanEqual) {
  const TypeParam a{2}, b{7};
  TNumericDataContainer num_container{a, "data"};
  EXPECT_LE(num_container, num_container);

  EXPECT_LE(num_container, b);
  EXPECT_LE(num_container, a);

  EXPECT_LE(a, num_container);
  EXPECT_LE(a - 1, num_container);

  TNumericDataContainer num_container2{b, "a"};
  TNumericDataContainer num_container3{b, "z"};
  EXPECT_LE(num_container, num_container2);
  EXPECT_LE(num_container, num_container3);

  TNumericDataContainer num_container4{a, "a"};
  TNumericDataContainer num_container5{a, "z"};
  EXPECT_LE(num_container, num_container4);
  EXPECT_LE(num_container, num_container5);
}

TYPED_TEST(TestNumericDataContainer, GreaterThan) {
  const TypeParam a{7}, b{2};
  TNumericDataContainer num_container{a, "data"};

  EXPECT_GT(num_container, b);
  EXPECT_GT(a + 1, num_container);

  TNumericDataContainer num_container2{b, "a"};
  TNumericDataContainer num_container3{b, "z"};
  EXPECT_GT(num_container, num_container2);
  EXPECT_GT(num_container, num_container3);
}

TYPED_TEST(TestNumericDataContainer, GreaterThanEqual) {
  const TypeParam a{7}, b{2};
  TNumericDataContainer num_container{a, "data"};
  EXPECT_GE(num_container, num_container);

  EXPECT_GE(num_container, b);
  EXPECT_GE(num_container, a);

  EXPECT_GE(a, num_container);
  EXPECT_GE(a + 1, num_container);

  TNumericDataContainer num_container2{b, "a"};
  TNumericDataContainer num_container3{b, "z"};
  EXPECT_GE(num_container, num_container2);
  EXPECT_GE(num_container, num_container3);

  TNumericDataContainer num_container4{a, "a"};
  TNumericDataContainer num_container5{a, "z"};
  EXPECT_GE(num_container, num_container4);
  EXPECT_GE(num_container, num_container5);
}

TYPED_TEST(TestNumericDataContainer, AdditionAssignment) {
  const TypeParam a{7}, b{2};
  TNumericDataContainer num_container{a, "data"};
  num_container += TNumericDataContainer{b, "data2"};
  EXPECT_EQ(num_container.numeric, a + b);
  EXPECT_EQ(num_container.data, "data");
}

TYPED_TEST(TestNumericDataContainer, SubtractionAssignment) {
  const TypeParam a{7}, b{2};
  TNumericDataContainer num_container{a, "data"};
  num_container -= TNumericDataContainer{b, "data2"};
  EXPECT_EQ(num_container.numeric, a - b);
  EXPECT_EQ(num_container.data, "data");
}

TYPED_TEST(TestNumericDataContainer, MultiplicationAssignment) {
  const TypeParam a{7}, b{2};
  TNumericDataContainer num_container{a, "data"};
  num_container *= TNumericDataContainer{b, "data2"};
  EXPECT_EQ(num_container.numeric, a * b);
  EXPECT_EQ(num_container.data, "data");
}

TYPED_TEST(TestNumericDataContainer, DivisionAssignment) {
  const TypeParam a{7}, b{2};
  TNumericDataContainer num_container{a, "data"};
  num_container /= TNumericDataContainer{b, "data2"};
  EXPECT_EQ(num_container.numeric, a / b);
  EXPECT_EQ(num_container.data, "data");
}

TYPED_TEST(TestNumericDataContainer, Addition) {
  const TypeParam a{7}, b{2};
  const TNumericDataContainer num_container{a, "data"};
  const TNumericDataContainer num_container2{b, "data2"};
  const TNumericDataContainer num_container3 = num_container + num_container2;
  EXPECT_EQ(num_container3.numeric, a + b);
  EXPECT_EQ(num_container3.data, "data");
}

TYPED_TEST(TestNumericDataContainer, Subtraction) {
  const TypeParam a{7}, b{2};
  const TNumericDataContainer num_container{a, "data"};
  const TNumericDataContainer num_container2{b, "data2"};
  const TNumericDataContainer num_container3 = num_container - num_container2;
  EXPECT_EQ(num_container3.numeric, a - b);
  EXPECT_EQ(num_container3.data, "data");
}

TYPED_TEST(TestNumericDataContainer, Multiplication) {
  const TypeParam a{7}, b{2};
  const TNumericDataContainer num_container{a, "data"};
  const TNumericDataContainer num_container2{b, "data2"};
  const TNumericDataContainer num_container3 = num_container * num_container2;
  EXPECT_EQ(num_container3.numeric, a * b);
  EXPECT_EQ(num_container3.data, "data");
}

TYPED_TEST(TestNumericDataContainer, Division) {
  const TypeParam a{7}, b{2};
  const TNumericDataContainer num_container{a, "data"};
  const TNumericDataContainer num_container2{b, "data2"};
  const TNumericDataContainer num_container3 = num_container / num_container2;
  EXPECT_EQ(num_container3.numeric, a / b);
  EXPECT_EQ(num_container3.data, "data");
}

TYPED_TEST(TestNumericDataContainer, Stdout) {
  EXPECT_NO_THROW(std::cout << (TNumericDataContainer{7, "data"}) << std::endl);
}
