/**
 * @file ArgParser.cpp
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 */
#include "BenchArgParser.h"

#include <utility>
#include <dirent.h>

using std::endl;
using std::cerr;
using std::string;
using std::ostream;
using std::string;

namespace dlinear::benchmark {
BenchArgParser::BenchArgParser() : parser_{DLINEAR_PROGRAM_NAME, DLINEAR_VERSION_STRING} {
  DLINEAR_LOG_INIT_VERBOSITY(-1);
  addOptions();
}

void BenchArgParser::parse(int argc, const char **argv) {
  try {
    parser_.parse_args(argc, argv);
    validateOptions();
  }
  catch (const std::runtime_error &err) {
    cerr << err.what() << endl;
    cerr << parser_;
    exit(EXIT_FAILURE);
  } catch (const std::invalid_argument &err) {
    cerr << err.what() << endl;
    cerr << parser_.usage() << endl;
    exit(EXIT_FAILURE);
  }
}

void BenchArgParser::addOptions() {
  parser_.add_description(prompt());
  parser_.add_argument("-d", "--dry-run")
      .help("whether to run in dry mode. No benchmarks are produced")
      .default_value(false)
      .implicit_value(true);
  parser_.add_argument("-t", "--timeout")
      .help("max time in seconds allowed for info gathering for each problem. "
            "Only problems taking less than the timeout are benchmarked. If set "
            "to 0, it is disabled.")
      .default_value(0u)
      .scan<'i', uint>();
  parser_.add_argument("-c", "--config")
      .help("path to the configuration file")
      .default_value(string{CONF_FILE});
  parser_.add_argument("-p", "--path")
      .help("path to the directory containing the smt2 files")
      .default_value(string{SMT2_DIR});
  parser_.add_argument("-f", "--file")
      .help("comma separated list of .smt2 files containing the problems to benchmark. If set, --path will be ignored.")
      .default_value(string{});
  parser_.add_argument("-e", "--extension")
      .help("extension of the files to be benchmarked")
      .default_value(string{".smt2"});
  parser_.add_argument("-o", "--output")
      .help("output file for the benchmark results. If not set, the results will be printed to stdout")
      .default_value(string{});
}

ostream &operator<<(ostream &os, const BenchArgParser &parser) {
  os << parser.parser_ << endl;
  return os;
}

BenchConfig BenchArgParser::toConfig() const {
  BenchConfig config{};
  config.setConfigFile(parser_.get<string>("config"));
  config.setPath(parser_.get<string>("path"));
  config.setDryRun(parser_.get<bool>("dry-run"));
  config.setTimeout(parser_.get<uint>("timeout"));
  config.setExtension(parser_.get<string>("extension"));
  config.setOutputFile(parser_.get<string>("output"));
  config.setFiles(getFilesVector());
  return config;
}

void BenchArgParser::validateOptions() {
  if (parser_.is_used("file") && parser_.is_used("path"))
    DLINEAR_INVALID_ARGUMENT("--path", "cannot be set if file is specified");
  if (parser_.is_used("file") && !file_exists(parser_.get<string>("file")))
    DLINEAR_INVALID_ARGUMENT("--file", fmt::format("file {} does not exist", parser_.get<string>("file")));
  if (!parser_.is_used("file") && !dir_exists(parser_.get<string>("path")))
    DLINEAR_INVALID_ARGUMENT("--path", fmt::format("directory {} does not exist", parser_.get<string>("path")));
  if (!file_exists(parser_.get<string>("config")))
    DLINEAR_INVALID_ARGUMENT("--config", fmt::format("file {} does not exist", parser_.get<string>("config")));
}

string BenchArgParser::version() const {
  return DLINEAR_VERSION_STRING;
}

string BenchArgParser::repositoryStatus() const {
  return DLINEAR_VERSION_REPOSTAT;
}

string BenchArgParser::prompt() const {
  return fmt::format("{} benchmark version {} ({})\n", DLINEAR_PROGRAM_NAME, version(), repositoryStatus());
}

std::vector<string> BenchArgParser::getFilesVector() const {
  std::vector<string> files = std::vector<string>{};
  if (parser_.is_used("file")) {
    files.push_back(parser_.get<string>("file"));
    return files;
  }

  DIR *dir;
  struct dirent *ent;
  string path = parser_.get<string>("path");
  string fileExtension = parser_.get<string>("extension");
  if ((dir = opendir(path.c_str())) != nullptr) {
    while ((ent = readdir(dir)) != nullptr) {
      if (EndsWith(ent->d_name, fileExtension.c_str()))
        files.push_back(fmt::format("{}/{}", path, ent->d_name));
    }
    closedir(dir);
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Could not open directory '{}' looking for '{}' files", path, fileExtension);
  }
  return files;
}

bool BenchArgParser::EndsWith(const char str[], const char suffix[]) const {
  size_t str_len = strlen(str), suffix_len = strlen(suffix);
  return suffix_len > 0 && str_len >= suffix_len &&
      0 == strncmp(str + str_len - suffix_len, suffix, suffix_len);
}

} // namespace dlinear
