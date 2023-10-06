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

  /**
   * @brief Initialize the array @p argv with the correct values, making it
   * ready to be used when starting a benchmark. The @p argv must have a size
   * greater or equal to 6. The value returned is intended to be used as the
   * argc parameter, and corresponds to the number of args in @p argv .
   * @param argv array to be initialized by the function
   * @param filename name of the file used in the benchmark
   * @param solver solver used in the benchmark
   * @param precision precision to use in the benchmark. If set to 0, enables
   * the --exhaustive flag
   * @return the argc parameter, meaning the size of usable arguments in @p argv
   */
  static inline int InitArgv(const char *argv[], const std::string &filename, const std::string &solver,
                             const std::string &precision);

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
