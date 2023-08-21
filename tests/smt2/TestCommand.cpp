/**
 * @file TestCommand.cpp
 * @author dlinear
 * @date 21 Aug 2023
 * @copyright 2023 dlinear
 */

#include "dlinear/smt2/Command.h"
#include "dlinear/smt2/CommandCell.h"

#include <gtest/gtest.h>

using dlinear::Command;
using dlinear::CommandCell;
using dlinear::exit_command;

TEST(TestCommand, Test) {
  EXPECT_NO_THROW(exit_command());
}