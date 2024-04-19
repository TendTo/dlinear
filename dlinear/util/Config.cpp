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
            << "continuous_output = " << config.continuous_output_.get() << ",\n"
            << "debug_parsing = " << config.debug_parsing_.get() << ",\n"
            << "debug_scanning = " << config.debug_scanning_.get() << ",\n"
            << "disable_theory_preprocessor = " << config.disable_theory_preprocessor_.get() << ",\n"
            << "enforce_check_sat = " << config.enforce_check_sat_.get() << ",\n"
            << "filename = '" << config.filename_.get() << "',\n"
            << "format = '" << config.format_.get() << "',\n"
            << "lp_mode = '" << config.lp_mode_.get() << "',\n"
            << "lp_solver = " << config.lp_solver_.get() << ",\n"
            << "nlopt_ftol_abs = " << config.nlopt_ftol_abs_.get() << ",\n"
            << "nlopt_ftol_rel = " << config.nlopt_ftol_rel_.get() << ",\n"
            << "nlopt_maxeval = " << config.nlopt_maxeval_.get() << ",\n"
            << "nlopt_maxtime = " << config.nlopt_maxtime_.get() << ",\n"
            << "number_of_jobs = " << config.number_of_jobs_.get() << ",\n"
            << "optimize = '" << config.optimize_.get() << "',\n"
            << "precision = " << config.precision_.get() << ",\n"
            << "produce_model = " << config.produce_models_.get() << ",\n"
            << "random_seed = " << config.random_seed_.get() << ",\n"
            << "read_from_stdin = " << config.read_from_stdin_.get() << ",\n"
            << "sat_default_phase = " << config.sat_default_phase_.get() << ",\n"
            << "silent = " << config.silent_.get() << ",\n"
            << "simplex_sat_phase = " << config.simplex_sat_phase_.get() << ",\n"
            << "use_local_optimization = " << config.use_local_optimization_.get() << ",\n"
            << "use_polytope = " << config.use_polytope_.get() << ",\n"
            << "use_polytope_in_forall = " << config.use_polytope_in_forall_.get() << ",\n"
            << "use_worklist_fixpoint = " << config.use_worklist_fixpoint_.get() << ",\n"
            << "verbose_dlinear = " << config.verbose_dlinear_.get() << ",\n"
            << "verbose_simplex = " << config.verbose_simplex_.get() << ",\n"
            << "with_timings = " << config.with_timings_.get() << ",\n"
            << '}';
}

}  // namespace dlinear
