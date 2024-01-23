/**
 * @file Config.h
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 * Config class.
 * Used to store the configuration of the program.
 *
 * Simple dataclass to store the configuration of the program.
 * It is generated from @ref ArgParser.
 */
#pragma once

#include <iostream>
#include <string>

#include "dlinear/util/OptionValue.hpp"

namespace dlinear {

#define DLINEAR_PARAMETER(param_name, type, default_value, help)               \
 public:                                                                       \
  OptionValue<type> &m_##param_name() { return param_name##_; }                \
  [[nodiscard]] const type &param_name() const { return param_name##_.get(); } \
  static constexpr type default_##param_name{default_value};                   \
  static constexpr const char *const help_##param_name{help};                  \
                                                                               \
 private:                                                                      \
  OptionValue<type> param_name##_{default_value};

class Config {
 public:
  enum class LPSolver {
    SOPLEX = 0,
    QSOPTEX = 1,
  };
  enum class SatDefaultPhase {
    False = 0,
    True = 1,
    JeroslowWang = 2,  ///< Default option
    RandomInitialPhase = 3
  };
  enum class Format {
    AUTO = 0,  ///< Default option
    SMT2 = 1,
    MPS = 2,
  };
  enum class LPMode {
    AUTO = 0,  ///< Default option
    PURE_PRECISION_BOOSTING = 1,
    PURE_ITERATIVE_REFINEMENT = 2,
    HYBRID = 3,
  };

  Config() = default;
  explicit Config(std::string filename);
  explicit Config(bool read_from_stdin);

 public:
  [[nodiscard]] std::string filename() const { return filename_.get(); }
  [[nodiscard]] std::string filename_extension() const;
  OptionValue<std::string> &m_filename() { return filename_; }
  static constexpr std::string_view help_filename{"Input file name"};

 private:
  OptionValue<std::string> filename_{""};

  DLINEAR_PARAMETER(format, Format, dlinear::Config::Format::AUTO, "Input file format")
  DLINEAR_PARAMETER(read_from_stdin, bool, false, "Read the input from the standard input")
  DLINEAR_PARAMETER(precision, double, 9.999999999999996e-4, "Delta precision used by the LP solver solver")
  DLINEAR_PARAMETER(produce_models, bool, false, "Produce models")
  DLINEAR_PARAMETER(use_polytope, bool, false, "Use polytope contractor")
  DLINEAR_PARAMETER(use_polytope_in_forall, bool, false, "Use polytope contractor in forall contractor")
  DLINEAR_PARAMETER(use_worklist_fixpoint, bool, false, "Use worklist fixpoint algorithm in ICP")
  DLINEAR_PARAMETER(use_local_optimization, bool, false, "Use local optimization algorithm for exist-forall problems")
  DLINEAR_PARAMETER(simplex_sat_phase, int, 1, "What phase to use to verify the feasibility of the LP problem")
  DLINEAR_PARAMETER(lp_mode, LPMode, dlinear::Config::LPMode::AUTO,
                    "LP mode used by the LP solver.\n"
                    "\t\t\tOne of: auto (0), pure-precision-boosting (1), pure-iterative-refinement (2), hybrid (3)")
  DLINEAR_PARAMETER(lp_solver, LPSolver, dlinear::Config::LPSolver::SOPLEX,
                    "LP solver used by the LP solver.\n"
                    "\t\t\tOne of: soplex (1), qsoptex (2)")
  DLINEAR_PARAMETER(verbose_simplex, int, 0, "Verbosity level for simplex. In the range [0, 5]")
  DLINEAR_PARAMETER(
      verbose_dlinear, int, 2,
      "Verbosity level for dlinear. In the range [0, 5]. 0 or any other value outside the range disables logging")
  DLINEAR_PARAMETER(continuous_output, bool, false, "Continuous output")
  DLINEAR_PARAMETER(with_timings, bool, false, "Report timings alongside results")
  DLINEAR_PARAMETER(number_of_jobs, uint, 1u, "Number of jobs")
  DLINEAR_PARAMETER(silent, bool, false, "Silent mode. Nothing will be printed on the standard output")
  DLINEAR_PARAMETER(nlopt_ftol_rel, double, 1e-6, "Set the relative tolerance on function value")
  DLINEAR_PARAMETER(nlopt_ftol_abs, double, 1e-6, "Set the absolute tolerance on function value")
  DLINEAR_PARAMETER(nlopt_maxeval, uint, 100u, "Set the maximum number of function evaluations")
  DLINEAR_PARAMETER(nlopt_maxtime, double, 0.01, "Set the maximum optimization time (in second)")
  DLINEAR_PARAMETER(sat_default_phase, SatDefaultPhase, dlinear::Config::SatDefaultPhase::JeroslowWang,
                    "set default initial phase for SAT solver.\n"
                    "\t\t\t0 = false\n"
                    "\t\t\t1 = true\n"
                    "\t\t\t2 = Jeroslow-Wang\n"
                    "\t\t\t3 = random initial phase\n\t\t\t")
  DLINEAR_PARAMETER(random_seed, uint, 0u, "Set the random seed. 0 means that the seed will be generated on the fly")
  DLINEAR_PARAMETER(debug_scanning, bool, false, "Debug scanning/lexing")
  DLINEAR_PARAMETER(debug_parsing, bool, false, "Debug parsing")
  DLINEAR_PARAMETER(skip_check_sat, bool, false, "Parse the input, but does not run the solver")

  friend std::ostream &operator<<(std::ostream &os, const Config &config);
};

std::ostream &operator<<(std::ostream &os, const Config::SatDefaultPhase &sat_default_phase);
std::ostream &operator<<(std::ostream &os, const Config::LPSolver &lp_solver);
std::ostream &operator<<(std::ostream &os, const Config::Format &format);
std::ostream &operator<<(std::ostream &os, const Config::LPMode &mode);

}  // namespace dlinear
