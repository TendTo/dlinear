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
  os << "Config {" << endl
     << "config_file = '" << config.config_file() << "', " << endl
     << "is_dry_run = '" << config.isDryRun() << "', " << endl
     << "timeout = '" << config.timeout() << "', " << endl
     << "path = '" << config.path() << "', " << endl
     << "files_provided = '" << config.filesProvided() << "', " << endl
     << "output_file = '" << config.output_file() << "', " << endl
     << "files" << " = [";
  for (const auto &file : config.files_) {
    os << file << ", ";
  }
  os << "] " << endl
     << '}';

  return os;
}
} // namespace dlinear
