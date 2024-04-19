/**
 * @file TestCommand.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "dlinear/parser/smt2/Command.h"
#include "dlinear/parser/smt2/CommandCell.h"

#include <gtest/gtest.h>

using dlinear::smt2::Command;
using dlinear::smt2::CommandCell;
using dlinear::smt2::exit_command;

TEST(TestCommand, Command) {
  EXPECT_NO_THROW(exit_command());
}