/**
 * @file BenchmarkProgram.cpp
 * @author dlinear
 * @date 28 Aug 2023
 * @copyright 2023 dlinear
 */

#include "BenchmarkProgram.h"

#include "benchmark/util/InfoGatherer.h"
#include "benchmark/util/BenchArgParser.h"

using std::string;
using std::vector;

namespace dlinear::benchmark {

BenchmarkProgram::BenchmarkProgram(int argc, const char *argv[]) : argc_{argc}, argv_{argv} {
  BenchArgParser arg_parser{};
  arg_parser.parse(argc, argv);
  config_ = arg_parser.toConfig();
}

int BenchmarkProgram::Run() {
  RegisterBenchmarks();
  return 0;
}

void BenchmarkProgram::RegisterBenchmarks() {
  ConfigFileReader config_file_reader{config_.config_file()};
  config_file_reader.read();

  std::stringstream ss;
  ss << "file,solver,assertions,precision,timeUnit,time,actualPrecision,result" << std::endl;

  std::cout << "Starting benchmarking" << std::endl;
  for (const string &filename : config_.files()) {
    for (const string &solver : config_file_reader.solvers()) {
      for (const string &precision : config_file_reader.precisions()) {
        InfoGatherer info_gatherer{filename, solver, precision, config_.timeout()};
        if (config_.isDryRun()) continue;
        if (info_gatherer.run() && info_gatherer.nAssertions() > 0) {
          ss << info_gatherer << std::endl;
        } else {

          std::cerr << "Could not gather info from " << filename << " with solver " << solver << " and precision "
                    << precision << std::endl;
        }
      }
    }
  }

  if (config_.output_file().empty()) {
    std::cout << ss.str();
  } else {
    std::ofstream output_file{config_.output_file()};
    output_file << ss.str();
    output_file.close();
  }
}

inline int BenchmarkProgram::InitArgv(const char *argv[],
                                      const string &filename,
                                      const string &solver,
                                      const string &precision) {
  int argc = DEFAULT_ARGC;
  argv[0] = "dlinear";
  argv[1] = filename.c_str();
  argv[2] = "--lp-solver";
  argv[3] = solver.c_str();
  if (stof(precision) == 0) {
    argv[4] = "--exhaustive";
    argc--;
  } else {
    argv[4] = "--precision";
    argv[5] = precision.c_str();
  }
  return argc;
}

} // namespace dlinear::benchmark