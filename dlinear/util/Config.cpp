/**
 * @file Config.cpp
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 */
#include "dlinear/util/Config.h"

namespace dlinear {

ostream &operator<<(ostream &os, const Config::SatDefaultPhase &sat_default_phase) {
  switch (sat_default_phase) {
    case Config::SatDefaultPhase::False:return os << "False";
    case Config::SatDefaultPhase::True:return os << "True";
    case Config::SatDefaultPhase::JeroslowWang:return os << "Jeroslow-Wang";
    case Config::SatDefaultPhase::RandomInitialPhase:return os << "Random Initial Phase";
    default: DLINEAR_UNREACHABLE();
  }
}

ostream &operator<<(ostream &os, const Config &config) {
  return os << "Config {" << endl
            << "filename = '" << config.filename_.get() << "', " << endl
            << "read_from_stdin = " << config.read_from_stdin_.get() << ", " << endl
            << "precision = " << config.precision_.get() << ", " << endl
            << "produce_model = " << config.produce_models_.get() << ", " << endl
            << "use_polytope = " << config.use_polytope_.get() << ", " << endl
            << "use_polytope_in_forall = " << config.use_polytope_in_forall_.get() << ", " << endl
            << "use_worklist_fixpoint = " << config.use_worklist_fixpoint_.get() << ", " << endl
            << "use_local_optimization = " << config.use_local_optimization_.get() << ", " << endl
            << "simplex_sat_phase = " << config.simplex_sat_phase_.get() << ", " << endl
            << "lp_solver = " << config.lp_solver_.get() << ", " << endl
            << "verbose_simplex = " << config.verbose_simplex_.get() << ", " << endl
            << "continuous_output = " << config.continuous_output_.get() << ", " << endl
            << "with_timings = " << config.with_timings_.get() << ", " << endl
            << "number_of_jobs = " << config.number_of_jobs_.get() << ", " << endl
            << "nlopt_ftol_rel = " << config.nlopt_ftol_rel_.get() << ", " << endl
            << "nlopt_ftol_abs = " << config.nlopt_ftol_abs_.get() << ", " << endl
            << "nlopt_maxeval = " << config.nlopt_maxeval_.get() << ", " << endl
            << "nlopt_maxtime = " << config.nlopt_maxtime_.get() << ", " << endl
            << "sat_default_phase = " << config.sat_default_phase_.get() << ", " << endl
            << "random_seed = " << config.random_seed_.get() << ", " << endl
            << '}';
}
} // namespace dlinear
