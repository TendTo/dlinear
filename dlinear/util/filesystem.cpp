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

using std::string;

namespace dlinear {

bool file_exists(const string &name) {
  DLINEAR_TRACE_FMT("file_exists({})", name);
  struct stat buffer{};
  if (stat(name.c_str(), &buffer) != 0)
    return false;
  return S_ISREG(buffer.st_mode);
}

bool dir_exists(const string &name) {
  DLINEAR_TRACE_FMT("dir_exists({})", name);
  struct stat buffer{};
  if (stat(name.c_str(), &buffer) != 0)
    return false;
  return S_ISDIR(buffer.st_mode);
}

string get_extension(const string &name) {
  DLINEAR_TRACE_FMT("get_extension({})", name);
  const size_t idx = name.rfind('.');
  DLINEAR_TRACE_FMT("position of the '.': {}", idx);
  if (idx == string::npos) // No extension found
    return "";
  return name.substr(idx + 1);
}

}  // namespace dlinear
