/**
 * @file Config.h
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 * Config class.
 * Used to store the configuration of the program.
 *
 * Simple dataclass to store the configuration of the program.
 * It is generated from @ref ArgParser.
 */
#pragma once

#include <iostream>
#include <string>
#include <vector>

#include "dlinear/util/Config.h"
#include "dlinear/util/exception.h"

namespace dlinear::benchmark {

#define DLINEAR_BENCHMARK_PARAMETER(param_name, type, default_value, help) \
 public:                                                                   \
  type &m_##param_name() { return param_name##_; }                         \
  [[nodiscard]] const type &param_name() const { return param_name##_; }   \
  static inline type default_##param_name{default_value};                  \
  static constexpr const char *const help_##param_name{help};              \
                                                                           \
 private:                                                                  \
  type param_name##_{default_value};

class BenchConfig {
 public:
  BenchConfig() = default;
  BenchConfig(const BenchConfig &) = default;
  BenchConfig(BenchConfig &&) = default;
  BenchConfig &operator=(const BenchConfig &) = default;
  BenchConfig &operator=(BenchConfig &&) = default;
  ~BenchConfig() = default;

  [[nodiscard]] bool are_files_provided() const { return !files_.empty(); }
  [[nodiscard]] std::vector<std::string> copyFiles() const { return files_; }

  DLINEAR_BENCHMARK_PARAMETER(is_dry_run, bool, false, "Whether to run in dry mode. No benchmarks are produced")
  DLINEAR_BENCHMARK_PARAMETER(timeout, uint, 0,
                              "Max time in seconds allowed for info gathering for each problem. "
                              "Only problems taking less than the timeout are benchmarked. If set "
                              "to 0, it is disabled.")
  DLINEAR_BENCHMARK_PARAMETER(config_file, std::string, "benchmark/benchmark.conf", "Path to the configuration file")
  DLINEAR_BENCHMARK_PARAMETER(path, std::string, "benchmark/smt2", "Path to the directory containing the problems")
  DLINEAR_BENCHMARK_PARAMETER(output_file, std::string, "", "Path to the output file")
  DLINEAR_BENCHMARK_PARAMETER(simplex_sat_phase, int, 1, "Simplex SAT phase to use. Must be either 1 or 2")
  DLINEAR_BENCHMARK_PARAMETER(files, std::vector<std::string>, {},
                              "List of files to benchmark. If specified, path is ignored")
  DLINEAR_BENCHMARK_PARAMETER(extension, std::string, "smt2", "Extension of the files to benchmark")
  DLINEAR_BENCHMARK_PARAMETER(info_verbosity, bool, false, "Apply the verbosity level INFO when running dlinear")

 private:
  friend std::ostream &operator<<(std::ostream &os, const BenchConfig &config);
};

}  // namespace dlinear::benchmark
