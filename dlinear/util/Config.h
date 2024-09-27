/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
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
  /** Underlying LP solver used by the theory solver. */
  enum class LPSolver {
    SOPLEX = 0,   ///< Soplex Solver. Default option
    QSOPTEX = 1,  ///< Qsoptex Solver
  };
  /** Underlying SAT solver used by the abstract SAT solver. */
  enum class SatSolver {
    CADICAL = 0,  ///< Cadical Solver. Default option
    PICOSAT = 1,  ///< Picosat Solver
  };
  /** Phase for the SAT solver. */
  enum class SatDefaultPhase {
    False = 0,              ///< Assign false to non fixed decision literals
    True = 1,               ///< Assign true to non fixed decision literals
    JeroslowWang = 2,       ///< Default option
    RandomInitialPhase = 3  ///< Randomly assign a value to non fixed decision literals
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
    PURE_PRECISION_BOOSTING = 1,    ///< Use the precision boosting mode, if available
    PURE_ITERATIVE_REFINEMENT = 2,  ///< Use the iterative refinement mode, if available
    HYBRID = 3,                     ///< Use both modes, if available
  };
  /** Types of bound propagation supported by the bound propagator */
  enum class BoundPropagationType {
    AUTO = 0,           ///< Automatically select the best configuration based on expected performance. Default option
    EQ_BINOMIAL = 1,    ///< Only propagate bounds in theory formulas in the form @f$ a x_1 + b x_2 = c @f$
    EQ_POLYNOMIAL = 2,  ///< Only propagate bound in theory formulae in the form @f$ \sum a_i x_i = c @f$
    BOUND_POLYNOMIAL = 3,  ///< Propagate all possible constraints
  };
  /** Frequency at which the preprocessors will run */
  enum class PreprocessingRunningFrequency {
    AUTO,          ///< Automatically select the best configuration based on expected performance. Default option
    NEVER,         ///< Never run this preprocess, effectively disabling it
    ON_FIXED,      ///< Run this preprocess only once, on fixed literals, before all iterations
    ON_ITERATION,  ///< Run this preprocess only at every iteration
    ALWAYS         /// Run this preprocess at every chance it gets. Usually combines ON_FIXED and ON_ITERATION
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
  /** @getsetter{`filename` extension, configuration, Contains the @ref filename substring after the dot.}*/
  OptionValue<std::string> &m_filename() { return filename_; }
  /** @getter{`onnx_file` parameter, configuration, Default to ""}*/
  [[nodiscard]] std::string onnx_file() const { return onnx_file_.get(); }
  /** @getsetter{`onnx_file` parameter, configuration, Default to ""}*/
  OptionValue<std::string> &m_onnx_file() { return onnx_file_; }
  /**
   * @getter{need for input expansion, configuration,
   * It is true when the input format is Format::SMT2 or Format::VNNLIB\, false if Format::MPS }
   */
  [[nodiscard]] bool needs_expansion() const;
  /**
   * @getter{actual `lp_mode` parameter, configuration,
     If the lp_mode is LPMode::AUTO\, it will return the appropriate mode based on the lp_solver}
   */
  [[nodiscard]] LPMode actual_lp_mode() const;
  /**
   * @getter{actual `format` parameter, configuration,
     If the format is Format::AUTO\, it will return the appropriate format based on the filename extension}
   */
  [[nodiscard]] Format actual_format() const;
  /**
   * @getter{actual `actual_bound_propagation_type` parameter, configuration,
     If the actual_bound_propagation_type is BoundPropagationType::AUTO\,
     it will return the appropriate bound propagation type based on the actual format}
   */
  [[nodiscard]] BoundPropagationType actual_bound_propagation_type() const;
  /**
   * @getter{actual `bound_propagation_frequency` parameter, configuration,
     If the bound_propagation_frequency is PreprocessingRunningFrequency::AUTO\,
     it will return the appropriate preprocessing running frequency based on the actual format}
   */
  [[nodiscard]] PreprocessingRunningFrequency actual_bound_propagation_frequency() const;
  /**
   * @getter{actual `bound_implication_frequency` parameter, configuration,
     If the bound_implication_frequency is PreprocessingRunningFrequency::AUTO\,
     it will return the appropriate preprocessing running frequency based on the actual format}
   */
  [[nodiscard]] PreprocessingRunningFrequency actual_bound_implication_frequency() const;

 private:
  OptionValue<std::string> filename_{""};
  OptionValue<std::string> onnx_file_{""};

  DLINEAR_PARAMETER(bound_propagation_type, BoundPropagationType, BoundPropagationType::AUTO,
                    "The type of bound propagation to apply in the preprocessing phase.\n"
                    "\t\tEach of the options is more complete and expensive than the previous one.\n"
                    "\t\tOne of: auto (1), eq-binomial (2), eq-polynomial (3), bound-polynomial (4)")
  DLINEAR_PARAMETER(bound_propagation_frequency, PreprocessingRunningFrequency, PreprocessingRunningFrequency::AUTO,
                    "How often to run the generic bound propagation preprocessing.\n"
                    "\t\tOne of: auto (1), never (2), on-fixed (3), on-iteration (4), always (5)")
  DLINEAR_PARAMETER(bound_implication_frequency, PreprocessingRunningFrequency, PreprocessingRunningFrequency::AUTO,
                    "How often to run the bound implication preprocessing.\n"
                    "\t\tOne of: auto (1), never (2), always (3)")
  DLINEAR_PARAMETER(complete, bool, false,
                    "Run the solver in complete mode.\n"
                    "\t\tThe precision will be set to 0 and strict inequalities will be taken into account")
  DLINEAR_PARAMETER(continuous_output, bool, false, "Continuous output")
  DLINEAR_PARAMETER(csv, bool, false, "Produce CSV output. Must also specify --with-timings to get the time stats")
  DLINEAR_PARAMETER(debug_parsing, bool, false, "Debug parsing")
  DLINEAR_PARAMETER(debug_scanning, bool, false, "Debug scanning/lexing")
  DLINEAR_PARAMETER(disable_expansion, bool, false,
                    "Disable formula expansion.\n"
                    "\t\tMakes the parser faster, "
                    "but may create issues if an intermediate formula of the input becomes non linear")
  DLINEAR_PARAMETER(
      enforce_check_sat, bool, false,
      "Perform a satisfiability check at the end of parsing if the input does not contain a (check-sat) directive")
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
  DLINEAR_PARAMETER(produce_models, bool, false,
                    "Produce models, showing a valid assignment.\n"
                    "\t\tOnly applicable if the result is sat or delta-sat")
  DLINEAR_PARAMETER(random_seed, unsigned int, 0u,
                    "Set the random seed. 0 means that the seed will be generated on the fly")
  DLINEAR_PARAMETER(read_from_stdin, bool, false, "Read the input from the standard input")
  DLINEAR_PARAMETER(sat_default_phase, SatDefaultPhase, dlinear::Config::SatDefaultPhase::JeroslowWang,
                    "set default initial phase for SAT solver.\n"
                    "\t\tOne of: false (0), true (1), Jeroslow-Wang (2), random initial phase (3)")
  DLINEAR_PARAMETER(sat_solver, SatSolver, dlinear::Config::SatSolver::PICOSAT,
                    "Underlying SAT solver used by the SAT solver.\n"
                    "\t\tOne of: cadical (1), picosat (2)")
  DLINEAR_PARAMETER(silent, bool, false, "Silent mode. Nothing will be printed on the standard output")
  DLINEAR_PARAMETER(simplex_sat_phase, int, 1, "What phase to use to verify the feasibility of the LP problem")
  DLINEAR_PARAMETER(skip_check_sat, bool, false, "Parse the input, but does not run the solver")
  DLINEAR_PARAMETER(verbose_dlinear, int, 2, "Verbosity level for dlinear. In the range [0, 5]")
  DLINEAR_PARAMETER(verbose_simplex, int, 0, "Verbosity level for simplex. In the range [0, 5]")
  DLINEAR_PARAMETER(verify, bool, false, "If the input produces a SAT output, verify the assignment against the input")
  DLINEAR_PARAMETER(with_timings, bool, false, "Report timings alongside results")
};

std::ostream &operator<<(std::ostream &os, const Config &config);
std::ostream &operator<<(std::ostream &os, const Config::SatDefaultPhase &sat_default_phase);
std::ostream &operator<<(std::ostream &os, const Config::LPSolver &lp_solver);
std::ostream &operator<<(std::ostream &os, const Config::SatSolver &mode);
std::ostream &operator<<(std::ostream &os, const Config::Format &format);
std::ostream &operator<<(std::ostream &os, const Config::LPMode &mode);
std::ostream &operator<<(std::ostream &os, const Config::BoundPropagationType &type);
std::ostream &operator<<(std::ostream &os, const Config::PreprocessingRunningFrequency &frequency);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT
#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::Config);
OSTREAM_FORMATTER(dlinear::Config::SatDefaultPhase);
OSTREAM_FORMATTER(dlinear::Config::LPSolver);
OSTREAM_FORMATTER(dlinear::Config::SatSolver);
OSTREAM_FORMATTER(dlinear::Config::Format);
OSTREAM_FORMATTER(dlinear::Config::LPMode);
OSTREAM_FORMATTER(dlinear::Config::BoundPropagationType);
OSTREAM_FORMATTER(dlinear::Config::PreprocessingRunningFrequency);

#endif
