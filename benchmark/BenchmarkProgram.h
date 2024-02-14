/**
 * @file BenchmarkProgram.h
 * @author dlinear
 * @date 28 Aug 2023
 * @copyright 2023 dlinear
 */
#pragma once

#include <string>
#include <vector>

#include "benchmark/util/BenchConfig.h"
#include "benchmark/util/ConfigFileReader.h"

namespace dlinear::benchmark {

class BenchmarkProgram {
 public:
  /**
   * @brief Create an instance of a BenchmarkProgram.
   * The object can than be used to run the benchmarks.
   * @param argc number of command line arguments. Passed by the main function
   * @param argv array of command line arguments. Passed by the main function
   */
  BenchmarkProgram(int argc, const char *argv[]);

  /**
   * @brief Run the benchmarks.
   * @return exit status
   */
  int Run();

 private:
  const static int DEFAULT_ARGC{6};
  int argc_;
  const char **argv_;
  BenchConfig config_;

  /** Start the benchmarking framework, making it run all registered benchmarks */
  void StartBenchmarks();

  void PrintRow(const std::string &row, bool overwrite = false);
};

}  // namespace dlinear::benchmark
