/**
 * @file TestFilesystem.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include <gtest/gtest.h>

#include <filesystem>
#include <fstream>

#include "dlinear/util/filesystem.h"

using dlinear::get_extension;
using std::ofstream;
using std::string;

TEST(TestFilesystem, GetExtension1) {
  const string f{"01.smt2"};
  EXPECT_EQ(get_extension(f), "smt2");
}

TEST(TestFilesystem, GetExtension2) {
  const string f{"abc_def.gh.smt2"};
  EXPECT_EQ(get_extension(f), "smt2");
}

TEST(TestFilesystem, GetExtension3) {
  const string f{"01.dr"};
  EXPECT_EQ(get_extension(f), "dr");
}

TEST(TestFilesystem, GetExtension4) {
  const string f{"123_456.789.dr"};
  EXPECT_EQ(get_extension(f), "dr");
}

TEST(TestFilesystem, GetExtension5) {
  const string f{"123_456_789"};
  EXPECT_EQ(get_extension(f), "");
}

TEST(TestFilesystem, FileExists) {
  string filename{"TempFile.test.cpp"};
  ofstream f{filename};
  EXPECT_TRUE(std::filesystem::is_regular_file(filename));
  remove(filename.c_str());
}

TEST(TestFilesystem, FileNotExists) {
  const string f{"TestFilesystem.cpp.not.exists"};
  EXPECT_FALSE(std::filesystem::is_regular_file(f));
}
