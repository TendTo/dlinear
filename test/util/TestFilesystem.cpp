/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include <gtest/gtest.h>

#include <filesystem>
#include <fstream>

#include "dlinear/util/filesystem.h"

using dlinear::GetExtension;
using std::ofstream;
using std::string;

TEST(TestFilesystem, GetExtension1) {
  const string f{"01.smt2"};
  EXPECT_EQ(GetExtension(f), "smt2");
}

TEST(TestFilesystem, GetExtension2) {
  const string f{"abc_def.gh.smt2"};
  EXPECT_EQ(GetExtension(f), "smt2");
}

TEST(TestFilesystem, GetExtension3) {
  const string f{"01.dr"};
  EXPECT_EQ(GetExtension(f), "dr");
}

TEST(TestFilesystem, GetExtension4) {
  const string f{"123_456.789.dr"};
  EXPECT_EQ(GetExtension(f), "dr");
}

TEST(TestFilesystem, GetExtension5) {
  const string f{"123_456_789"};
  EXPECT_EQ(GetExtension(f), "");
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
