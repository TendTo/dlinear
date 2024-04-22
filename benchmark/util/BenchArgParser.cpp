/**
 * @file ArgParser.cpp
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 */
#include "BenchArgParser.h"

#include <dirent.h>
#include <fmt/fmt.h>

#include <filesystem>

namespace dlinear::benchmark {

#define DLINEAR_BENCHMARK_PARSE_PARAM_BOOL(parser, name, ...)           \
  do {                                                                  \
    parser.add_argument(__VA_ARGS__)                                    \
        .help(dlinear::benchmark::BenchConfig::help_##name)             \
        .default_value(dlinear::benchmark::BenchConfig::default_##name) \
        .implicit_value(true);                                          \
  } while (false)

#define DLINEAR_BENCHMARK_PARSE_PARAM_SCAN(parser, name, scan_char, scan_type, ...) \
  do {                                                                              \
    parser.add_argument(__VA_ARGS__)                                                \
        .help(dlinear::benchmark::BenchConfig::help_##name)                         \
        .default_value(dlinear::benchmark::BenchConfig::default_##name)             \
        .scan<scan_char, scan_type>();                                              \
  } while (false)

#define DLINEAR_BENCHMARK_PARSE_PARAM(parser, name, ...)                 \
  do {                                                                   \
    parser.add_argument(__VA_ARGS__)                                     \
        .help(dlinear::benchmark::BenchConfig::help_##name)              \
        .default_value(dlinear::benchmark::BenchConfig::default_##name); \
  } while (false)

BenchArgParser::BenchArgParser() : parser_{DLINEAR_PROGRAM_NAME, DLINEAR_VERSION_STRING} {
  DLINEAR_LOG_INIT_VERBOSITY(-1);
  addOptions();
}

void BenchArgParser::parse(int argc, const char **argv) {
  try {
    parser_.parse_args(argc, argv);
    validateOptions();
  } catch (const std::runtime_error &err) {
    std::cerr << err.what() << std::endl;
    std::cerr << parser_;
    exit(EXIT_FAILURE);
  } catch (const std::invalid_argument &err) {
    std::cerr << err.what() << std::endl;
    std::cerr << parser_.usage() << std::endl;
    exit(EXIT_FAILURE);
  }
}

void BenchArgParser::addOptions() {
  parser_.add_description(prompt());
  DLINEAR_BENCHMARK_PARSE_PARAM_BOOL(parser_, is_dry_run, "-d", "--dry-run");
  DLINEAR_BENCHMARK_PARSE_PARAM_BOOL(parser_, info_verbosity, "--info-verbosity");

  DLINEAR_BENCHMARK_PARSE_PARAM_SCAN(parser_, timeout, 'i', uint, "-t", "--timeout");
  DLINEAR_BENCHMARK_PARSE_PARAM_SCAN(parser_, simplex_sat_phase, 'i', int, "-s", "--simplex-sat-phase");

  DLINEAR_BENCHMARK_PARSE_PARAM(parser_, config_file, "-c", "--config");
  DLINEAR_BENCHMARK_PARSE_PARAM(parser_, path, "-p", "--path");
  DLINEAR_BENCHMARK_PARSE_PARAM(parser_, output_file, "-o", "--output");
  DLINEAR_BENCHMARK_PARSE_PARAM(parser_, extension, "-e", "--extension");

  parser_.add_argument("-f", "--file").help("File to benchmark").default_value(std::string{});
}

std::ostream &operator<<(std::ostream &os, const BenchArgParser &parser) {
  os << parser.parser_ << std::endl;
  return os;
}

BenchConfig BenchArgParser::toConfig() const {
  BenchConfig config{};
  config.m_config_file() = parser_.get<std::string>("config");
  config.m_path() = parser_.get<std::string>("path");
  config.m_is_dry_run() = parser_.get<bool>("dry-run");
  config.m_timeout() = parser_.get<uint>("timeout");
  config.m_extension() = parser_.get<std::string>("extension");
  config.m_output_file() = parser_.get<std::string>("output");
  config.m_simplex_sat_phase() = parser_.get<int>("simplex-sat-phase");
  config.m_files() = getFilesVector();
  if (parser_.get<bool>("info-verbosity"))
    DLINEAR_LOG_INIT_VERBOSITY(3);
  else
    DLINEAR_LOG_INIT_VERBOSITY(0);
  return config;
}

void BenchArgParser::validateOptions() {
  if (parser_.is_used("file") && parser_.is_used("path"))
    DLINEAR_INVALID_ARGUMENT("--path", "cannot be set if file is specified");
  if (parser_.is_used("file") && !std::filesystem::is_regular_file(parser_.get<std::string>("file")))
    DLINEAR_INVALID_ARGUMENT("--file", fmt::format("file {} does not exist", parser_.get<std::string>("file")));
  if (!parser_.is_used("file") && !std::filesystem::is_directory(parser_.get<std::string>("path")))
    DLINEAR_INVALID_ARGUMENT("--path", fmt::format("directory {} does not exist", parser_.get<std::string>("path")));
  if (!std::filesystem::is_regular_file(parser_.get<std::string>("config")))
    DLINEAR_INVALID_ARGUMENT("--config", fmt::format("file {} does not exist", parser_.get<std::string>("config")));
  if (parser_.get<int>("simplex-sat-phase") != 1 && parser_.get<int>("simplex-sat-phase") != 2)
    DLINEAR_INVALID_ARGUMENT("--simplex-sat-phase", fmt::format("value must be either 1 or 2, received '{}'",
                                                                parser_.get<int>("simplex-sat-phase")));
}

std::string BenchArgParser::version() { return DLINEAR_VERSION_STRING; }

std::string BenchArgParser::repositoryStatus() { return DLINEAR_VERSION_REPOSTAT; }

std::string BenchArgParser::prompt() {
  return fmt::format("{} benchmark version {} ({})\n", DLINEAR_PROGRAM_NAME, version(), repositoryStatus());
}

std::vector<std::string> BenchArgParser::getFilesVector() const {
  std::vector<std::string> files = std::vector<std::string>{};
  if (parser_.is_used("file")) {
    files.push_back(parser_.get<std::string>("file"));
    return files;
  }

  DIR *dir;
  struct dirent *ent;
  std::string path = parser_.get<std::string>("path");
  std::string fileExtension = parser_.get<std::string>("extension");
  if ((dir = opendir(path.c_str())) != nullptr) {
    while ((ent = readdir(dir)) != nullptr) {
      if (EndsWith(ent->d_name, fileExtension.c_str())) files.push_back(fmt::format("{}/{}", path, ent->d_name));
    }
    closedir(dir);
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Could not open directory '{}' looking for '{}' files", path, fileExtension);
  }
  return files;
}

bool BenchArgParser::EndsWith(const char str[], const char suffix[]) {
  size_t str_len = strlen(str), suffix_len = strlen(suffix);
  return suffix_len > 0 && str_len >= suffix_len && 0 == strncmp(str + str_len - suffix_len, suffix, suffix_len);
}

}  // namespace dlinear::benchmark
