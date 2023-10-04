/**
 * @file TestVariable.cpp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 */

#include <gtest/gtest.h>

#include "dlinear/symbolic/Variable.h"

using dlinear::symbolic::Variable;

TEST(TestVariable, DummyVariableContructor) {
  const Variable dummy{};
  EXPECT_TRUE(dummy.is_dummy());
  EXPECT_EQ(dummy.get_id(), 0);
  EXPECT_TRUE(dummy.get_name().empty());
}

TEST(TestVariable, VariableContructor) {
  const Variable var{"var"};
  EXPECT_FALSE(var.is_dummy());
  EXPECT_GT(var.get_id(), 0);
  EXPECT_TRUE(var.get_name() == "var");
}
