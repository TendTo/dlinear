/**
 * @file TestFilesystem.cpp
 * @author dlinear
 * @date 16 Aug 2023
 * @copyright 2023 dlinear
 */
#include "dlinear/util/filesystem.h"

#include <filesystem>
#include <gtest/gtest.h>

using std::string;
using std::filesystem::directory_iterator;
using dlinear::get_extension;
using dlinear::file_exists;

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
  for (const auto &entry : directory_iterator(".")) {
    if (entry.is_regular_file()) {
      EXPECT_TRUE(file_exists(entry.path().string()));
    }
  }
}

TEST(TestFilesystem, FileNotExists) {
  const string f{"TestFilesystem.cpp.not.exists"};
  EXPECT_FALSE(file_exists(f));
}


