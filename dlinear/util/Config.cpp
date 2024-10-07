/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "Config.h"

#include <iostream>
#include <utility>

#include "dlinear/util/exception.h"
#include "dlinear/util/filesystem.h"

namespace dlinear {
Config::Config(std::string filename) : filename_{std::move(filename)} {}
Config::Config(bool read_from_stdin) : read_from_stdin_{read_from_stdin} {}

std::string Config::filename_extension() const { return get_extension(filename_.get()); }

bool Config::needs_expansion() const {
  if (disable_expansion_.get()) return false;
  const Format format = actual_format();
  return format == Format::VNNLIB || format == Format::SMT2;
}
Config::LPMode Config::actual_lp_mode() const {
  switch (lp_mode_.get()) {
    case LPMode::AUTO:
      return lp_solver_.get() == LPSolver::QSOPTEX ? LPMode::PURE_PRECISION_BOOSTING : LPMode::HYBRID;
    default:
      return lp_mode_.get();
  }
}
Config::Format Config::actual_format() const {
  switch (format_.get()) {
    case Format::AUTO:
      if (filename_extension() == "mps") {
        return Format::MPS;
      } else if (filename_extension() == "smt2") {
        return Format::SMT2;
      } else if (filename_extension() == "vnnlib") {
        return Format::VNNLIB;
      }
      DLINEAR_RUNTIME_ERROR("Cannot determine format from stdin or unknown file extension");
    default:
      return format_.get();
  }
}
Config::BoundPropagationType Config::actual_bound_propagation_type() const {
  switch (bound_propagation_type_.get()) {
    case BoundPropagationType::AUTO:
      switch (actual_format()) {
        case Format::SMT2:
          return BoundPropagationType::EQ_POLYNOMIAL;
        case Format::MPS:
          return BoundPropagationType::EQ_BINOMIAL;
        case Format::VNNLIB:
          return BoundPropagationType::BOUND_POLYNOMIAL;
        default:
          DLINEAR_UNREACHABLE();
      }
    default:
      return bound_propagation_type_.get();
  }
}
Config::PreprocessingRunningFrequency Config::actual_bound_propagation_frequency() const {
  switch (bound_propagation_frequency_.get()) {
    case PreprocessingRunningFrequency::AUTO:
      switch (actual_format()) {
        case Format::SMT2:
          return PreprocessingRunningFrequency::ALWAYS;
        case Format::MPS:
          return PreprocessingRunningFrequency::NEVER;
        case Format::VNNLIB:
          return PreprocessingRunningFrequency::ALWAYS;
        default:
          DLINEAR_UNREACHABLE();
      }
    default:
      return bound_propagation_frequency_.get();
  }
}
Config::PreprocessingRunningFrequency Config::actual_bound_implication_frequency() const {
  switch (bound_implication_frequency_.get()) {
    case PreprocessingRunningFrequency::AUTO:
      switch (actual_format()) {
        case Format::SMT2:
          return PreprocessingRunningFrequency::ALWAYS;
        case Format::MPS:
        case Format::VNNLIB:
          return PreprocessingRunningFrequency::NEVER;
        default:
          DLINEAR_UNREACHABLE();
      }
    default:
      return bound_implication_frequency_.get();
  }
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
      return os << "A";
    case Config::LPMode::PURE_PRECISION_BOOSTING:
      return os << "P";
    case Config::LPMode::PURE_ITERATIVE_REFINEMENT:
      return os << "I";
    case Config::LPMode::HYBRID:
      return os << "H";
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::ostream &operator<<(std::ostream &os, const Config::BoundPropagationType &type) {
  switch (type) {
    case Config::BoundPropagationType::AUTO:
      return os << "auto";
    case Config::BoundPropagationType::EQ_BINOMIAL:
      return os << "eq-binomial";
    case Config::BoundPropagationType::EQ_POLYNOMIAL:
      return os << "eq-polynomial";
    case Config::BoundPropagationType::BOUND_POLYNOMIAL:
      return os << "bound-polynomial";
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::ostream &operator<<(std::ostream &os, const Config::PreprocessingRunningFrequency &frequency) {
  switch (frequency) {
    case Config::PreprocessingRunningFrequency::AUTO:
      return os << "auto";
    case Config::PreprocessingRunningFrequency::NEVER:
      return os << "never";
    case Config::PreprocessingRunningFrequency::ON_FIXED:
      return os << "on-fixed";
    case Config::PreprocessingRunningFrequency::ON_ITERATION:
      return os << "on-iteration";
    case Config::PreprocessingRunningFrequency::ALWAYS:
      return os << "always";
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::ostream &operator<<(std::ostream &os, const Config &config) {
  return os << "Config {\n"
            << "bound_implication_frequency = " << config.bound_implication_frequency() << ",\n"
            << "bound_propagation_frequency = " << config.bound_propagation_frequency() << ",\n"
            << "bound_propagation_type = " << config.bound_propagation_type() << ",\n"
            << "csv = " << config.csv() << ",\n"
            << "complete = " << config.complete() << ",\n"
            << "continuous_output = " << config.continuous_output() << ",\n"
            << "debug_parsing = " << config.debug_parsing() << ",\n"
            << "debug_scanning = " << config.debug_scanning() << ",\n"
            << "disable_expansion = " << config.disable_expansion() << ",\n"
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
            << "verify = " << config.verify() << ",\n"
            << "with_timings = " << config.with_timings() << ",\n"
            << '}';
}

}  // namespace dlinear
