/**
 * @file ConfigFileReader.cpp
 * @author dlinear
 * @date 28 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */

#include "ConfigFileReader.h"
#include "dlinear/util/exception.h"

#include <fstream>
#include <regex>

using std::string;

namespace dlinear::benchmark {

void ConfigFileReader::read() {
  std::ifstream conf_file{configFile_};
  if (!conf_file.is_open())
    DLINEAR_RUNTIME_ERROR_FMT("File '{}' could not be opened", configFile_);

  const std::regex conf_regex("^(\\w+) *= *(.+?) *$");
  std::smatch conf_matches;
  string line;

  while (conf_file) {
    std::getline(conf_file, line);

    if (std::regex_match(line, conf_matches, conf_regex)) {
      if (conf_matches.size() != 3) continue;

      string parameter = conf_matches[1].str();
      std::stringstream values{conf_matches[2].str()};
      string value;
      while (values >> value) parameters_[parameter].push_back(value);
    }
  }
}

std::ostream &operator<<(std::ostream &os, const ConfigFileReader &configFileReader) {
  os << "ConfigFileReader{" << "parameters_= {" << std::endl;
  for (auto mapIt = begin(configFileReader.parameters_); mapIt != end(configFileReader.parameters_); ++mapIt) {
    os << mapIt->first << " : ";
    for (const auto &c : mapIt->second) {
      os << c << " ";
    }
    os << std::endl;
  }
  os << "}";
  return os;
}
} // namespace dlinear::benchmark
