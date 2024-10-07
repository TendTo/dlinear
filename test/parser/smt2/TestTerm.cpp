/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gtest/gtest.h>

#include "dlinear/parser/smt2/Term.h"

using dlinear::Expression;
using dlinear::Formula;
using dlinear::smt2::Term;

class TestTerm : public ::testing::Test {
 protected:
  const Formula f_{};
  const Expression e_{};
};

TEST_F(TestTerm, FormulaConstructor) {
  Term term{f_};
  EXPECT_EQ(term.type(), Term::Type::FORMULA);
  EXPECT_TRUE(term.formula().EqualTo(f_));
  EXPECT_THROW(Expression a = term.expression(), std::bad_variant_access);
}

TEST_F(TestTerm, ExpressionConstructor) {
  Term term{e_};
  EXPECT_EQ(term.type(), Term::Type::EXPRESSION);
  EXPECT_TRUE(term.expression().EqualTo(e_));
  EXPECT_THROW(Formula f = term.formula(), std::bad_variant_access);
}
