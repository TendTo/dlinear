/**
 * @file ArgParser.h
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 * ArgParser class.
 * Used to parse command line arguments.
 *
 * Parse the command line arguments and convert them to Config.
 * The config object will then be used throughout the program.
 * The default values are defined in the configuration of the parser.
 */
#ifndef DLINEAR5_BENCHMARK_UTIL_BENCHARGPARSER_H_
#define DLINEAR5_BENCHMARK_UTIL_BENCHARGPARSER_H_

#include <dirent.h>

#include <iostream>
#include <string>

#include <argparse/argparse.hpp>

#include "benchmark/util/BenchConfig.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"
#include "dlinear/util/filesystem.h"
#include "dlinear/version.h"

#define CONF_FILE "benchmark/benchmark.conf"
#define SMT2_DIR "benchmark/smt2"

namespace dlinear::benchmark {

class BenchArgParser {
 private:
  argparse::ArgumentParser parser_;

  void addOptions();

  void validateOptions();

  /**
   * @brief Load all the files found in the path parameter matching the provided
   * fileExtension and return them as a vector of strings.
   * @return vector of strings containing the files found in the path parameter
   */
  [[nodiscard]] std::vector<std::string> getFilesVector() const;

  bool EndsWith(const char str[], const char suffix[]) const;

 public:
  BenchArgParser();

  void parse(int argc, const char **argv);

  [[nodiscard]] std::string version() const;

  [[nodiscard]] std::string repositoryStatus() const;

  [[nodiscard]] std::string prompt() const;

  friend std::ostream &operator<<(std::ostream &os, const BenchArgParser &parser);

  [[nodiscard]] BenchConfig toConfig() const;

  template<typename T = std::string>
  [[nodiscard]] T get(const std::string &key) const { return parser_.get<T>(key); }

  friend std::ostream &operator<<(std::ostream &os, const BenchArgParser &parser);
};

} // namespace dlinear



#endif //DLINEAR5_BENCHMARK_UTIL_BENCHARGPARSER_H_
