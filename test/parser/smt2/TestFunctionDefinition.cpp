/**
 * @file TestFunctionDefinition.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include "dlinear/parser/smt2/FunctionDefinition.h"
#include "test/symbolic/TestSymbolicUtils.h"

using dlinear::Expression;
using dlinear::Variable;
using dlinear::smt2::FunctionDefinition;
using dlinear::smt2::ParseSort;
using dlinear::smt2::Sort;
using dlinear::smt2::SortToType;
using dlinear::smt2::Term;
using std::runtime_error;

class TestFunctionDefinition : public ::testing::TestWithParam<bool> {
 protected:
  const double min_val_ = 5, max_val_ = 6;
  const Variable lhs_{"lhs"}, rhs_{"rhs"};
  const Variable x_{"x"}, y_{"y"}, z_{"z"};
  const double a_val_ = 2, b_val_ = 3, c_val_ = 5;
};

INSTANTIATE_TEST_SUITE_P(TestFunctionDefinition, TestFunctionDefinition, ::testing::Values(false, true));

TEST_P(TestFunctionDefinition, MaxFunctionDefinition) {
  const Expression body = if_then_else(lhs_ > rhs_, lhs_, rhs_);
  const FunctionDefinition fun{{lhs_, rhs_}, Sort::Real, Term{body}};

  const auto res = GetParam() ? fun(Term{min_val_}, Term{max_val_}) : fun({Term{min_val_}, Term{max_val_}});

  EXPECT_EQ(res.type(), Term::Type::EXPRESSION);
  EXPECT_TRUE(is_constant(res.expression()));
  EXPECT_EQ(get_constant_value(res.expression()), std::max(min_val_, max_val_));
}

TEST_P(TestFunctionDefinition, MinFunctionDefinition) {
  const Expression body = if_then_else(lhs_ < rhs_, lhs_, rhs_);
  const FunctionDefinition fun{{lhs_, rhs_}, Sort::Real, Term{body}};

  const Term res = GetParam() ? fun(Term{min_val_}, Term{max_val_}) : fun({Term{min_val_}, Term{max_val_}});

  EXPECT_EQ(res.type(), Term::Type::EXPRESSION);
  EXPECT_TRUE(is_constant(res.expression()));
  EXPECT_EQ(get_constant_value(res.expression()), std::min(min_val_, max_val_));
}

TEST_P(TestFunctionDefinition, SumFunctionDefinition) {
  const Expression body = lhs_ + rhs_;
  const FunctionDefinition fun{{lhs_, rhs_}, Sort::Real, Term{body}};

  const Term res = GetParam() ? fun(Term{min_val_}, Term{max_val_}) : fun({Term{min_val_}, Term{max_val_}});

  EXPECT_EQ(res.type(), Term::Type::EXPRESSION);
  EXPECT_TRUE(is_constant(res.expression()));
  EXPECT_EQ(get_constant_value(res.expression()), min_val_ + max_val_);
}

TEST_P(TestFunctionDefinition, SubFunctionDefinition) {
  const Expression body = x_ - y_ - z_;
  const FunctionDefinition fun{{x_, y_, z_}, Sort::Real, Term{body}};

  const Term res =
      GetParam() ? fun(Term{a_val_}, Term{b_val_}, Term{c_val_}) : fun({Term{a_val_}, Term{b_val_}, Term{c_val_}});

  EXPECT_EQ(res.type(), Term::Type::EXPRESSION);
  EXPECT_TRUE(is_constant(res.expression()));
  EXPECT_EQ(get_constant_value(res.expression()), a_val_ - b_val_ - c_val_);
}
