/**
 * @file BenchmarkProgram.cpp
 * @author dlinear
 * @date 28 Aug 2023
 * @copyright 2023 dlinear
 */

#include "BenchmarkProgram.h"

#include <fstream>

#include "benchmark/util/BenchArgParser.h"
#include "benchmark/util/InfoGatherer.h"

namespace dlinear::benchmark {

namespace {

inline dlinear::Config GetConfig(const std::string &filename, const Config::LPSolver solver, const double precision,
                                 int simplex_phase, const Config::LPMode lp_mode = Config::LPMode::AUTO) {
  dlinear::Config config{filename};
  config.m_lp_solver().set_from_command_line(solver);
  config.m_precision().set_from_command_line(precision);
  config.m_simplex_sat_phase().set_from_command_line(simplex_phase);
  config.m_lp_mode().set_from_command_line(lp_mode);
  return config;
}

inline bool ValidConfig(const dlinear::Config &config) {
  if (config.lp_solver() == Config::LPSolver::QSOPTEX) {
    return config.lp_mode() == Config::LPMode::AUTO || config.lp_mode() == Config::LPMode::PURE_PRECISION_BOOSTING;
  }
  return true;
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
  for (const std::string &filename : config_.files()) {
    for (Config::LPSolver solver : config_file.solvers()) {
      for (double precision : config_file.precisions()) {
        for (Config::LPMode lp_mode : config_file.lp_modes()) {
          dlinear::Config dlinear_config{GetConfig(filename, solver, precision, config_.simplex_sat_phase(), lp_mode)};
          if (!ValidConfig(dlinear_config)) continue;
          InfoGatherer info_gatherer{dlinear_config, config_.timeout()};
          if (config_.is_dry_run()) continue;
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

}  // namespace dlinear::benchmark