/**
 * @file Config.h
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 * Config class.
 * Used to store the configuration of the program.
 *
 * Simple dataclass used to store the configuration of the program.
 * It is generated from @ref dlinear::ArgParser.
 */
#pragma once

#include <iostream>
#include <string>
#include <string_view>

#include "dlinear/util/OptionValue.hpp"
#include "dlinear/util/logging.h"

namespace dlinear {

#define DLINEAR_PARAMETER(param_name, type, default_value, help)                           \
 public:                                                                                   \
  /** @getter{`##param_name##` parameter, configuration, Default to default_value##} */    \
  OptionValue<type> &m_##param_name() { return param_name##_; }                            \
  /** @getsetter{`##param_name##` parameter, configuration, Default to default_value##} */ \
  [[nodiscard]] const type &param_name() const { return param_name##_.get(); }             \
  static constexpr type default_##param_name{default_value};                               \
  static constexpr const char *const help_##param_name{help};                              \
                                                                                           \
 private:                                                                                  \
  OptionValue<type> param_name##_{default_value};

/**
 * Simple dataclass used to store the configuration of the program.
 *
 * It is usually generated by the @ref ArgParser using the command line arguments.
 */
class Config {
 public:
  /**
   * Underlying LP solver used by the theory solver.
   * @see Config::lp_solver
   */
  enum class LPSolver {
    SOPLEX = 0,   ///< Soplex Solver. Default option
    QSOPTEX = 1,  ///< Qsoptex Solver
  };
  /**
   * Underlying SAT solver used by the abstract SAT solver.
   * @see Config::sat_solver
   */
  enum class SatSolver {
    CADICAL = 0,  ///< Cadical Solver. Default option
    PICOSAT = 1,  ///< Picosat Solver
  };
  /** Default phase for the SAT solver. */
  enum class SatDefaultPhase {
    False = 0,
    True = 1,
    JeroslowWang = 2,  ///< Default option
    RandomInitialPhase = 3
  };
  /** Format of the input file. */
  enum class Format {
    AUTO,   ///< Automatically detect the input format based on the file extension. Default option
    SMT2,   ///< SMT2 format
    MPS,    ///< MPS format
    VNNLIB  ///< VNNLIB format
  };
  /** LP mode used by the LP solver. */
  enum class LPMode {
    AUTO = 0,                       ///< Let the LP solver choose the mode. Default option
    PURE_PRECISION_BOOSTING = 1,    ///< Use the precision boosting mode
    PURE_ITERATIVE_REFINEMENT = 2,  ///< Use the iterative refinement mode
    HYBRID = 3,                     ///< Use both modes, if available
  };

  /** @constructor{Config} */
  Config() = default;
  /**
   * Construct a new Config object with the given filename.
   * @param filename name of the input file
   */
  explicit Config(std::string filename);
  /**
   * Construct a new Config object that will read the input from the standard input.
   * @param read_from_stdin whether to read the input from the standard input
   */
  explicit Config(bool read_from_stdin);

 public:
  static constexpr std::string_view help_onnx_file{"ONNX file name"};
  static constexpr std::string_view help_filename{"Input file name"};

  /** @getter{`filename` parameter, configuration, Default to ""}*/
  [[nodiscard]] std::string filename() const { return filename_.get(); }
  /** @getter{`filename` extension, configuration, Contains the @ref filename substring after the dot.}*/
  [[nodiscard]] std::string filename_extension() const;
  OptionValue<std::string> &m_filename() { return filename_; }
  [[nodiscard]] std::string onnx_file() const { return onnx_file_.get(); }
  OptionValue<std::string> &m_onnx_file() { return onnx_file_; }
  /**
   * @getter{need for input expansion, configuration,
   * It is true when the input format is Format::SMT2 or Format::VNNLIB\, false if Format::MPS }
   */
  [[nodiscard]] bool needs_expansion() const;

 private:
  OptionValue<std::string> filename_{""};
  OptionValue<std::string> onnx_file_{""};

  DLINEAR_PARAMETER(complete, bool, false,
                    "Run the solver in complete mode.\n"
                    "\t\tThe precision will be set to 0 and strict inequalities will be used taken into account")
  DLINEAR_PARAMETER(continuous_output, bool, false, "Continuous output")
  DLINEAR_PARAMETER(debug_parsing, bool, false, "Debug parsing")
  DLINEAR_PARAMETER(debug_scanning, bool, false, "Debug scanning/lexing")
  DLINEAR_PARAMETER(disable_eq_propagation, bool, false, "Disable the propagation of equality constraints")
  DLINEAR_PARAMETER(disable_bound_propagation, bool, false, "Disable the propagation of bounds among constraints")
  DLINEAR_PARAMETER(disable_theory_preprocessing, bool, false,
                    "Disable the addition of constraints based on theory propagation")
  DLINEAR_PARAMETER(
      enforce_check_sat, bool, false,
      "Perform a satisfiability check at the end of the parsing if the input does not contain a (check-sat) directive")
  DLINEAR_PARAMETER(format, Format, dlinear::Config::Format::AUTO,
                    "Input file format\n"
                    "\t\tOne of: auto (1), smt2 (2), mps (3), vnnlib (4)")
  DLINEAR_PARAMETER(lp_mode, LPMode, dlinear::Config::LPMode::AUTO,
                    "LP mode used by the LP solver.\n"
                    "\t\tOne of: auto (1), pure-precision-boosting (2), pure-iterative-refinement (3), hybrid (4)")
  DLINEAR_PARAMETER(lp_solver, LPSolver, dlinear::Config::LPSolver::SOPLEX,
                    "Underlying LP solver used by the theory solver.\n"
                    "\t\tOne of: soplex (1), qsoptex (2)")
  DLINEAR_PARAMETER(number_of_jobs, unsigned int, 1u, "Number of jobs")
  DLINEAR_PARAMETER(optimize, bool, false, "Whether to optimize the objective function. Only affects the MPS format")
  DLINEAR_PARAMETER(precision, double, 9.999999999999996e-4,
                    "Delta precision used by the LP solver solver.\n"
                    "\t\tEven when set to 0, a positive infinitesimal value will be considered.\n"
                    "\t\twhile the LP solver will yield an exact solution, strict inequalities will still be relaxed\n"
                    "\t\tUse the --complete flag if you are looking for a complete solution")
  DLINEAR_PARAMETER(produce_models, bool, false, "Produce models")
  DLINEAR_PARAMETER(random_seed, unsigned int, 0u,
                    "Set the random seed. 0 means that the seed will be generated on the fly")
  DLINEAR_PARAMETER(read_from_stdin, bool, false, "Read the input from the standard input")
  DLINEAR_PARAMETER(sat_default_phase, SatDefaultPhase, dlinear::Config::SatDefaultPhase::JeroslowWang,
                    "set default initial phase for SAT solver.\n"
                    "\t\tOne of: false (0), true (1), Jeroslow-Wang (2), random initial phase (3)")
  DLINEAR_PARAMETER(sat_solver, SatSolver, dlinear::Config::SatSolver::CADICAL,
                    "Underlying SAT solver used by the SAT solver.\n"
                    "\t\tOne of: cadical (1), picosat (2)")
  DLINEAR_PARAMETER(silent, bool, false, "Silent mode. Nothing will be printed on the standard output")
  DLINEAR_PARAMETER(simplex_sat_phase, int, 1, "What phase to use to verify the feasibility of the LP problem")
  DLINEAR_PARAMETER(skip_check_sat, bool, false, "Parse the input, but does not run the solver")
  DLINEAR_PARAMETER(verbose_dlinear, int, 2, "Verbosity level for dlinear. In the range [0, 5]")
  DLINEAR_PARAMETER(verbose_simplex, int, 0, "Verbosity level for simplex. In the range [0, 5]")
  DLINEAR_PARAMETER(with_timings, bool, false, "Report timings alongside results")
};

std::ostream &operator<<(std::ostream &os, const Config &config);
std::ostream &operator<<(std::ostream &os, const Config::SatDefaultPhase &sat_default_phase);
std::ostream &operator<<(std::ostream &os, const Config::LPSolver &lp_solver);
std::ostream &operator<<(std::ostream &os, const Config::SatSolver &mode);
std::ostream &operator<<(std::ostream &os, const Config::Format &format);
std::ostream &operator<<(std::ostream &os, const Config::LPMode &mode);

}  // namespace dlinear

OSTREAM_FORMATTER(dlinear::Config::SatDefaultPhase)
OSTREAM_FORMATTER(dlinear::Config::LPSolver)
OSTREAM_FORMATTER(dlinear::Config::SatSolver)
OSTREAM_FORMATTER(dlinear::Config::Format)
OSTREAM_FORMATTER(dlinear::Config::LPMode)
OSTREAM_FORMATTER(dlinear::Config)
