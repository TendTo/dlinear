/**
 * @file Config.cpp
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 */
#include "Config.h"

#include <utility>

#include "dlinear/util/exception.h"
#include "dlinear/util/filesystem.h"

namespace dlinear {
Config::Config(std::string filename) : filename_{std::move(filename)} {}
Config::Config(bool read_from_stdin) : read_from_stdin_{read_from_stdin} {}

std::string Config::filename_extension() const { return get_extension(filename_.get()); }

bool Config::needs_expansion() const {
  return format() == Config::Format::SMT2 || format() == Config::Format::VNNLIB || filename_extension() == "smt2" ||
         filename_extension() == "vnnlib";
}

std::ostream &operator<<(std::ostream &os, const Config::SatDefaultPhase &sat_default_phase) {
  switch (sat_default_phase) {
    case Config::SatDefaultPhase::False:
      return os << "False";
    case Config::SatDefaultPhase::True:
      return os << "True";
    case Config::SatDefaultPhase::JeroslowWang:
      return os << "Jeroslow-Wang";
    case Config::SatDefaultPhase::RandomInitialPhase:
      return os << "Random Initial Phase";
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::ostream &operator<<(std::ostream &os, const Config::LPSolver &lp_solver) {
  switch (lp_solver) {
    case Config::LPSolver::QSOPTEX:
      return os << "qsoptex";
    case Config::LPSolver::SOPLEX:
      return os << "soplex";
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::ostream &operator<<(std::ostream &os, const Config::SatSolver &sat_solver) {
  switch (sat_solver) {
    case Config::SatSolver::CADICAL:
      return os << "cadical";
    case Config::SatSolver::PICOSAT:
      return os << "picosat";
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::ostream &operator<<(std::ostream &os, const Config::Format &format) {
  switch (format) {
    case Config::Format::AUTO:
      return os << "auto";
    case Config::Format::MPS:
      return os << "mps";
    case Config::Format::SMT2:
      return os << "smt2";
    case Config::Format::VNNLIB:
      return os << "vnnlib";
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::ostream &operator<<(std::ostream &os, const Config::LPMode &mode) {
  switch (mode) {
    case Config::LPMode::AUTO:
      return os << "auto";
    case Config::LPMode::PURE_PRECISION_BOOSTING:
      return os << "pure-precision-boosting";
    case Config::LPMode::PURE_ITERATIVE_REFINEMENT:
      return os << "pure-iterative-refinement";
    case Config::LPMode::HYBRID:
      return os << "hybrid";
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::ostream &operator<<(std::ostream &os, const Config &config) {
  return os << "Config {\n"
            << "csv = " << config.csv() << ",\n"
            << "complete = " << config.complete() << ",\n"
            << "continuous_output = " << config.continuous_output() << ",\n"
            << "debug_parsing = " << config.debug_parsing() << ",\n"
            << "debug_scanning = " << config.debug_scanning() << ",\n"
            << "disable_eq_propagation = " << config.disable_eq_propagation() << ",\n"
            << "disable_bound_propagation = " << config.disable_bound_propagation() << ",\n"
            << "disable_theory_preprocessing = " << config.disable_theory_preprocessing() << ",\n"
            << "enforce_check_sat = " << config.enforce_check_sat() << ",\n"
            << "filename = '" << config.filename() << "',\n"
            << "format = '" << config.format() << "',\n"
            << "lp_mode = '" << config.lp_mode() << "',\n"
            << "lp_solver = " << config.lp_solver() << ",\n"
            << "number_of_jobs = " << config.number_of_jobs() << ",\n"
            << "onnx_file = '" << config.onnx_file() << ",\n"
            << "optimize = '" << config.optimize() << "',\n"
            << "precision = " << config.precision() << ",\n"
            << "produce_model = " << config.produce_models() << ",\n"
            << "random_seed = " << config.random_seed() << ",\n"
            << "read_from_stdin = " << config.read_from_stdin() << ",\n"
            << "sat_default_phase = " << config.sat_default_phase() << ",\n"
            << "sat_solver = " << config.sat_solver() << ",\n"
            << "silent = " << config.silent() << ",\n"
            << "simplex_sat_phase = " << config.simplex_sat_phase() << ",\n"
            << "skip_check_sat = " << config.skip_check_sat() << ",\n"
            << "verbose_dlinear = " << config.verbose_dlinear() << ",\n"
            << "verbose_simplex = " << config.verbose_simplex() << ",\n"
            << "with_timings = " << config.with_timings() << ",\n"
            << '}';
}

}  // namespace dlinear
