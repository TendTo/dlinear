/**
 * @file BenchmarkProgram.cpp
 * @author dlinear
 * @date 28 Aug 2023
 * @copyright 2023 dlinear
 */

#include "BenchmarkProgram.h"

#include "benchmark/util/BenchArgParser.h"
#include "benchmark/util/InfoGatherer.h"

using std::string;
using std::vector;

namespace dlinear::benchmark {

namespace {

inline dlinear::Config GetConfig(const string &filename, const string &solver, const string &precision,
                                 int simplex_phase, const string &lp_mode = "auto") {
  dlinear::Config config{filename};
  config.m_lp_solver().set_from_command_line(InfoGatherer::GetLPSolver(solver));
  config.m_precision().set_from_command_line(stod(precision));
  config.m_simplex_sat_phase().set_from_command_line(simplex_phase);
  config.m_lp_mode().set_from_command_line(InfoGatherer::GetLPMode(lp_mode));
  return config;
}

}  // namespace

BenchmarkProgram::BenchmarkProgram(int argc, const char *argv[]) : argc_{argc}, argv_{argv} {
  BenchArgParser arg_parser{};
  arg_parser.parse(argc, argv);
  config_ = arg_parser.toConfig();
}

int BenchmarkProgram::Run() {
  StartBenchmarks();
  return 0;
}

void BenchmarkProgram::PrintRow(const std::string &row, bool overwrite) {
  if (config_.output_file().empty()) {
    std::cout << row << std::endl;
  } else {
    std::ofstream output_file{config_.output_file(), overwrite ? std::ofstream::trunc : std::ofstream::app};
    output_file << row << std::endl;
    output_file.close();
  }
}

void BenchmarkProgram::StartBenchmarks() {
  ConfigFileReader config_file{config_.config_file()};
  config_file.read();

  PrintRow(
      "file,solver,assertions,precision,simplexPhase,lpMode,timeUnit,time,parserTime,smtTime,actualPrecision,result",
      true);

  std::cout << "Starting benchmarking" << std::endl;
  for (const string &filename : config_.files()) {
    for (const string &solver : config_file.solvers()) {
      for (const string &precision : config_file.precisions()) {
        for (const string &lp_mode : config_file.lp_modes()) {
          dlinear::Config dlinear_config{GetConfig(filename, solver, precision, config_.simplex_sat_phase(), lp_mode)};
          if (dlinear_config.lp_solver() == Config::LPSolver::QSOPTEX &&
              dlinear_config.lp_mode() != Config::LPMode::AUTO)
            continue;
          InfoGatherer info_gatherer{dlinear_config, config_.timeout()};
          if (config_.isDryRun()) continue;
          if (info_gatherer.run() && info_gatherer.nAssertions() > 0) {
            PrintRow((std::stringstream{} << info_gatherer).str());
          } else {
            std::cerr << "Could not gather info from " << filename << " with solver " << solver << ", precision "
                      << precision << ", lp_mode " << lp_mode << std::endl;
          }
        }
      }
    }
  }
}

inline int BenchmarkProgram::InitArgv(const char *argv[], const string &filename, const string &solver,
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

}  // namespace dlinear::benchmark