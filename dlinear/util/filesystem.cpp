/**
 * @file filesystem.cpp
 * @author dlinear
 * @date 15 Aug 2023
 * @copyright 2023 dlinear
 */

#include "filesystem.h"

#include <cstddef>
#include <filesystem>

#include "dlinear/util/logging.h"

namespace dlinear {

std::string get_extension(const std::string &name) {
  DLINEAR_TRACE_FMT("get_extension({})", name);
  const std::size_t idx = name.rfind('.');
  DLINEAR_TRACE_FMT("position of the '.': {}", idx);
  if (idx == std::string::npos)  // No extension found
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
