/**
 * @file TestOptionValue.cpp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 */

#include "dlinear/util/OptionValue.hpp"

#include <gtest/gtest.h>

using dlinear::OptionValue;

TEST(TestConfig, Constructor) {
  OptionValue<int> ov{3};
  EXPECT_EQ(ov.get(), 3);
}

TEST(TestConfig, SetFromFile) {
  OptionValue<int> ov{3};
  EXPECT_EQ(ov.get(), 3);
  ov.set_from_file(4);
  EXPECT_EQ(ov.get(), 4);
}

TEST(TestConfig, SetFromCmdLine) {
  OptionValue<int> ov{3};
  EXPECT_EQ(ov.get(), 3);
  ov.set_from_command_line(4);
  EXPECT_EQ(ov.get(), 4);
}

TEST(TestConfig, SetFromCode) {
  OptionValue<int> ov{3};
  EXPECT_EQ(ov.get(), 3);
  ov = 4;
  EXPECT_EQ(ov.get(), 4);
}

TEST(TestConfig, CodePriorityOverFile) {
  OptionValue<int> ov{3};
  EXPECT_EQ(ov.get(), 3);
  ov = 4;
  EXPECT_EQ(ov.get(), 4);
  ov.set_from_file(5);
  EXPECT_EQ(ov.get(), 4);
}

TEST(TestConfig, CodePriorityOverCmdLine) {
  OptionValue<int> ov{3};
  EXPECT_EQ(ov.get(), 3);
  ov = 4;
  EXPECT_EQ(ov.get(), 4);
  ov.set_from_command_line(5);
  EXPECT_EQ(ov.get(), 4);
}

TEST(TestConfig, CmdLinePriorityOverFile) {
  OptionValue<int> ov{3};
  EXPECT_EQ(ov.get(), 3);
  ov.set_from_command_line(4);
  EXPECT_EQ(ov.get(), 4);
  ov.set_from_file(5);
  EXPECT_EQ(ov.get(), 4);
}
