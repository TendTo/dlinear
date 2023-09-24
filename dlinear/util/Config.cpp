/**
 * @file Config.cpp
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 */
#include "Config.h"

#include "dlinear/util/exception.h"
#include "dlinear/util/filesystem.h"

using std::endl;
using std::ostream;

namespace dlinear {
Config::Config(const std::string filename) : filename_{filename} {}
Config::Config(bool read_from_stdin) : read_from_stdin_{read_from_stdin} {}

std::string Config::filename_extension() const { return get_extension(filename_.get()); }

ostream &operator<<(ostream &os, const Config::SatDefaultPhase &sat_default_phase) {
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

ostream &operator<<(ostream &os, const Config &config) {
  return os << "Config {" << endl
            << "continuous_output = " << config.continuous_output_.get() << ", " << endl
            << "debug_parsing = " << config.debug_parsing_.get() << ", " << endl
            << "debug_scanning = " << config.debug_scanning_.get() << ", " << endl
            << "filename = '" << config.filename_.get() << "', " << endl
            << "format = '" << config.format_.get() << "', " << endl
            << "lp_solver = " << config.lp_solver_.get() << ", " << endl
            << "nlopt_ftol_abs = " << config.nlopt_ftol_abs_.get() << ", " << endl
            << "nlopt_ftol_rel = " << config.nlopt_ftol_rel_.get() << ", " << endl
            << "nlopt_maxeval = " << config.nlopt_maxeval_.get() << ", " << endl
            << "nlopt_maxtime = " << config.nlopt_maxtime_.get() << ", " << endl
            << "number_of_jobs = " << config.number_of_jobs_.get() << ", " << endl
            << "precision = " << config.precision_.get() << ", " << endl
            << "produce_model = " << config.produce_models_.get() << ", " << endl
            << "random_seed = " << config.random_seed_.get() << ", " << endl
            << "read_from_stdin = " << config.read_from_stdin_.get() << ", " << endl
            << "sat_default_phase = " << config.sat_default_phase_.get() << ", " << endl
            << "silent = " << config.silent_.get() << ", " << endl
            << "simplex_sat_phase = " << config.simplex_sat_phase_.get() << ", " << endl
            << "use_local_optimization = " << config.use_local_optimization_.get() << ", " << endl
            << "use_polytope = " << config.use_polytope_.get() << ", " << endl
            << "use_polytope_in_forall = " << config.use_polytope_in_forall_.get() << ", " << endl
            << "use_worklist_fixpoint = " << config.use_worklist_fixpoint_.get() << ", " << endl
            << "verbose_dlinear = " << config.verbose_dlinear_.get() << ", " << endl
            << "verbose_simplex = " << config.verbose_simplex_.get() << ", " << endl
            << "with_timings = " << config.with_timings_.get() << ", " << endl
            << '}';
}

}  // namespace dlinear
