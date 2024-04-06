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

std::string Config::filename_extension() const { return get_extension(filename_.get()); }

bool Config::needs_expansion() const { return format() == Config::Format::SMT2 || filename_extension() == "smt2"; }

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

std::ostream &operator<<(std::ostream &os, const Config::Format &format) {
  switch (format) {
    case Config::Format::AUTO:
      return os << "auto";
    case Config::Format::MPS:
      return os << "mps";
    case Config::Format::SMT2:
      return os << "smt2";
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
            << "continuous_output = " << config.continuous_output() << ",\n"
            << "debug_parsing = " << config.debug_parsing() << ",\n"
            << "debug_scanning = " << config.debug_scanning() << ",\n"
            << "disable_theory_preprocessor = " << config.disable_theory_preprocessor() << ",\n"
            << "enforce_check_sat = " << config.enforce_check_sat() << ",\n"
            << "filename = '" << config.filename() << "',\n"
            << "format = '" << config.format() << "',\n"
            << "lp_mode = '" << config.lp_mode() << "',\n"
            << "lp_solver = " << config.lp_solver() << ",\n"
            << "nlopt_ftol_abs = " << config.nlopt_ftol_abs() << ",\n"
            << "nlopt_ftol_rel = " << config.nlopt_ftol_rel() << ",\n"
            << "nlopt_maxeval = " << config.nlopt_maxeval() << ",\n"
            << "nlopt_maxtime = " << config.nlopt_maxtime() << ",\n"
            << "number_of_jobs = " << config.number_of_jobs() << ",\n"
            << "optimize = '" << config.optimize() << "',\n"
            << "precision = " << config.precision() << ",\n"
            << "produce_model = " << config.produce_models() << ",\n"
            << "random_seed = " << config.random_seed() << ",\n"
            << "read_from_stdin = " << config.read_from_stdin() << ",\n"
            << "sat_default_phase = " << config.sat_default_phase() << ",\n"
            << "silent = " << config.silent() << ",\n"
            << "simplex_sat_phase = " << config.simplex_sat_phase() << ",\n"
            << "use_local_optimization = " << config.use_local_optimization() << ",\n"
            << "use_polytope = " << config.use_polytope() << ",\n"
            << "use_polytope_in_forall = " << config.use_polytope_in_forall() << ",\n"
            << "use_worklist_fixpoint = " << config.use_worklist_fixpoint() << ",\n"
            << "verbose_dlinear = " << config.verbose_dlinear() << ",\n"
            << "verbose_simplex = " << config.verbose_simplex() << ",\n"
            << "with_timings = " << config.with_timings() << ",\n"
            << '}';
}

}  // namespace dlinear
