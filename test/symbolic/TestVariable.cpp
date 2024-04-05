/**
 * @file TestVariable.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include "dlinear/symbolic/Variable.h"

using dlinear::symbolic::Variable;

class TestVariable : public ::testing::Test {
 protected:
  const Variable x_{"x"};
  const Variable i_{"i", Variable::Type::INTEGER};
  const Variable b_{"b", Variable::Type::BOOLEAN};

  ~TestVariable() override {
    EXPECT_FALSE(x_.is_dummy());
    EXPECT_EQ(x_.name(), "x");
    EXPECT_EQ(x_.type(), Variable::Type::CONTINUOUS);

    EXPECT_FALSE(i_.is_dummy());
    EXPECT_EQ(i_.name(), "i");
    EXPECT_EQ(i_.type(), Variable::Type::INTEGER);

    EXPECT_FALSE(b_.is_dummy());
    EXPECT_EQ(b_.name(), "b");
    EXPECT_EQ(b_.type(), Variable::Type::BOOLEAN);
  }
};

TEST_F(TestVariable, DummyConstructor) {
  const Variable x;
  EXPECT_TRUE(x.is_dummy());
  EXPECT_EQ(x.name(), "d");
  EXPECT_EQ(x.type(), Variable::Type::CONTINUOUS);
}

TEST_F(TestVariable, StandardConstructorContinuous) {
  const std::string name{"x"};
  const Variable x{name};
  EXPECT_FALSE(x.is_dummy());
  EXPECT_EQ(x.name(), name);
  EXPECT_EQ(x.type(), Variable::Type::CONTINUOUS);
}

TEST_F(TestVariable, StandardConstructorBoolean) {
  const std::string name{"b"};
  const Variable b{name, Variable::Type::BOOLEAN};
  EXPECT_FALSE(b.is_dummy());
  EXPECT_EQ(b.name(), name);
  EXPECT_EQ(b.type(), Variable::Type::BOOLEAN);
}

TEST_F(TestVariable, CopyConstructor) {
  const Variable i{i_};
  EXPECT_FALSE(i.is_dummy());
  EXPECT_EQ(i.name(), i.name());
  EXPECT_EQ(i.type(), i.type());
}

TEST_F(TestVariable, MoveConstructor) {
  Variable i{i_};
  const Variable j{std::move(i)};
  EXPECT_FALSE(j.is_dummy());
  EXPECT_EQ(j.name(), i_.name());
  EXPECT_EQ(j.type(), i_.type());

  EXPECT_TRUE(i.is_dummy());
  EXPECT_EQ(i.name(), "d");
  EXPECT_EQ(i.type(), Variable::Type::CONTINUOUS);
}

TEST_F(TestVariable, CopyAssignment) {
  Variable i;
  i = i_;
  EXPECT_FALSE(i.is_dummy());
  EXPECT_EQ(i.name(), i.name());
  EXPECT_EQ(i.type(), i_.type());
}

TEST_F(TestVariable, MoveAssignment) {
  Variable i{i_};
  Variable j;
  j = std::move(i);

  EXPECT_FALSE(j.is_dummy());
  EXPECT_EQ(j.name(), i_.name());
  EXPECT_EQ(j.type(), i_.type());

  EXPECT_TRUE(i.is_dummy());
  EXPECT_EQ(i.name(), "d");
  EXPECT_EQ(i.type(), Variable::Type::CONTINUOUS);
}

TEST_F(TestVariable, Equality) {
  const Variable x1{"var"};
  const Variable y{"var"};
  const Variable b{"b", Variable::Type::BOOLEAN};

  EXPECT_FALSE(x1.equal_to(y));
  EXPECT_FALSE(x1.equal_to(y));
}

TEST_F(TestVariable, Less) {
  const Variable x{"var"};
  const Variable y{"var"};
  const Variable b{"b", Variable::Type::BOOLEAN};

  EXPECT_FALSE(x.less(x));
  EXPECT_TRUE(x.less(y));
  EXPECT_FALSE(y.less(x));
  EXPECT_TRUE(y.less(b));
  EXPECT_FALSE(b.less(y));
  EXPECT_FALSE(b.less(x));
}

TEST_F(TestVariable, Hash) {
  const Variable x{"var"};
  const Variable y{"var"};
  const Variable b{"b", Variable::Type::BOOLEAN};

  EXPECT_EQ(x.hash(), x.hash());
  EXPECT_EQ(x.hash(), std::hash<Variable::Id>{}(x.id()));
  EXPECT_NE(x.hash(), y.hash());
  EXPECT_NE(x.hash(), b.hash());
  EXPECT_NE(y.hash(), b.hash());
}

TEST_F(TestVariable, ToString) {
  const Variable x{"x"};
  EXPECT_EQ(x.ToString(), "x");
}

TEST_F(TestVariable, ToStringDummy) {
  const Variable x;
  EXPECT_EQ(x.ToString(), "d");
}

TEST_F(TestVariable, Ostream) { EXPECT_NO_THROW(std::cout << x_ << std::endl); }
