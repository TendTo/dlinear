/**
 * @file filesystem.cpp
 * @author dlinear
 * @date 15 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */

#include "filesystem.h"

#include <sys/stat.h>

#include <filesystem>

#include "dlinear/util/logging.h"

using std::string;

namespace dlinear {

bool file_exists(const string &name) {
  DLINEAR_TRACE_FMT("file_exists({})", name);
  struct stat buffer {};
  if (stat(name.c_str(), &buffer) != 0) return false;
  return S_ISREG(buffer.st_mode);
}

bool dir_exists(const string &name) {
  DLINEAR_TRACE_FMT("dir_exists({})", name);
  struct stat buffer {};
  if (stat(name.c_str(), &buffer) != 0) return false;
  return S_ISDIR(buffer.st_mode);
}

string get_extension(const string &name) {
  DLINEAR_TRACE_FMT("get_extension({})", name);
  const size_t idx = name.rfind('.');
  DLINEAR_TRACE_FMT("position of the '.': {}", idx);
  if (idx == string::npos)  // No extension found
    return "";
  return name.substr(idx + 1);
}

std::vector<std::string> split_string_by_whitespace(const char *in) {
  std::vector<std::string> r;
  for (const char *p = in; *p; ++p) {
    while (*p == ' ' || *p == '\t' || *p == '\r') ++p;
    if (*p == '\0') break;
    int length = 0;
    while (p[length] != ' ' && p[length] != '\t' && p[length] != '\r' && p[length]) ++length;
    r.emplace_back(p, length);
    p += length - 1;
  }
  return r;
}

std::vector<std::string> get_files(const std::string &path) {
  std::vector<std::string> files;
  for (const auto &entry : std::filesystem::directory_iterator(path)) files.emplace_back(entry.path());
  return files;
}

}  // namespace dlinear
