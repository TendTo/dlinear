/**
 * @file Config.cpp
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 */
#include "BenchConfig.h"

using std::endl;
using std::ostream;

namespace dlinear::benchmark {

ostream &operator<<(ostream &os, const BenchConfig &config) {
  os << "Config {\n"
     << "config_file = '" << config.config_file() << "', \n"
     << "is_dry_run = '" << config.is_dry_run() << "', \n"
     << "timeout = '" << config.timeout() << "', \n"
     << "path = '" << config.path() << "', \n"
     << "are_files_provided = '" << config.are_files_provided() << "', \n"
     << "output_file = '" << config.output_file() << "', \n"
     << "files = [";
  for (const auto &file : config.files_) {
    os << file << ", ";
  }
  os << "] \n}";

  return os;
}
}  // namespace dlinear::benchmark
