/**
 * @file TestTerm.cpp
 * @author dlinear
 * @date 21 Aug 2023
 * @copyright 2023 dlinear
 */

#include "dlinear/smt2/Term.h"

#include <gtest/gtest.h>

using dlinear::Formula;
using dlinear::Expression;
using dlinear::Term;
using std::runtime_error;

class TestTerm : public ::testing::Test {
 protected:
  const Formula f_{};
  const Expression e_{};
};

TEST_F(TestTerm, FormulaConstructor) {
  Term term{f_};
  EXPECT_EQ(term.type(), Term::Type::FORMULA);
  EXPECT_TRUE(term.formula().EqualTo(f_));
  EXPECT_THROW(term.expression(), runtime_error);
}

TEST_F(TestTerm, ExpressionConstructor) {
  Term term{e_};
  EXPECT_EQ(term.type(), Term::Type::EXPRESSION);
  EXPECT_TRUE(term.expression().EqualTo(e_));
  EXPECT_THROW(term.formula(), runtime_error);
}

