/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
// IWYU pragma: no_include "argparse/argparse.hpp" // Already included in the header
#include "ArgParser.h"

#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <stdexcept>

#ifdef DLINEAR_ENABLED_QSOPTEX
#include "dlinear/libs/libqsopt_ex.h"
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
#include "dlinear/libs/libsoplex.h"
#endif

#include "dlinear/util/OptionValue.hpp"
#include "dlinear/util/exception.h"
#include "dlinear/util/filesystem.h"
#include "dlinear/util/logging.h"
#include "dlinear/version.h"

namespace dlinear {

#define DLINEAR_PARSE_PARAM_BOOL(parser, name, ...)        \
  do {                                                     \
    parser.add_argument(__VA_ARGS__)                       \
        .help(dlinear::Config::help_##name)                \
        .default_value(dlinear::Config::default_##name)    \
        .implicit_value(!dlinear::Config::default_##name); \
  } while (false)

#define DLINEAR_PARSE_PARAM_SCAN(parser, name, scan_char, scan_type, ...) \
  do {                                                                    \
    parser.add_argument(__VA_ARGS__)                                      \
        .help(dlinear::Config::help_##name)                               \
        .default_value(dlinear::Config::default_##name)                   \
        .nargs(1)                                                         \
        .scan<scan_char, scan_type>();                                    \
  } while (false)

#define DLINEAR_PARSE_PARAM_ENUM(parser, name, cmd_name, invalid_prompt, ...) \
  do {                                                                        \
    parser.add_argument(cmd_name)                                             \
        .help(dlinear::Config::help_##name)                                   \
        .default_value(dlinear::Config::default_##name)                       \
        .action([](const std::string &value) {                                \
          __VA_ARGS__                                                         \
          DLINEAR_INVALID_ARGUMENT_EXPECTED(cmd_name, value, invalid_prompt); \
        })                                                                    \
        .nargs(1);                                                            \
  } while (false)

#define DLINEAR_PARAM_TO_CONFIG(param_name, config_name, type)                                                      \
  do {                                                                                                              \
    if (parser_.is_used(param_name)) config.m_##config_name().set_from_command_line(parser_.get<type>(param_name)); \
  } while (false)

ArgParser::ArgParser()
    : parser_{DLINEAR_PROGRAM_NAME, DLINEAR_VERSION_STRING},
      verbosity_{Config::default_verbose_dlinear},
#ifdef DLINEAR_ENABLED_QSOPTEX
      qsoptex_hash_{QSopt_ex_repository_status()},
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
      soplex_hash_{soplex::getGitHash()}  // NOLINT(whitespace/braces)
#endif
{
  DLINEAR_TRACE("ArgParser::ArgParser");
  addOptions();
}

void ArgParser::parse(int argc, const char **argv) {
  try {
    parser_.parse_args(argc, argv);
    DLINEAR_LOG_INIT_VERBOSITY((parser_.get<bool>("silent") ? 0 : verbosity_));
    validateOptions();
    DLINEAR_TRACE("ArgParser::parse: parsed args");
  } catch (const std::runtime_error &err) {
    std::cerr << err.what() << "\n" << parser_ << std::endl;
    std::exit(EXIT_FAILURE);
  } catch (const std::invalid_argument &err) {
    std::cerr << err.what() << "\n\n" << parser_.usage() << std::endl;
    std::exit(EXIT_FAILURE);
  }
}

void ArgParser::addOptions() {
  DLINEAR_TRACE("ArgParser::addOptions: adding options");
  parser_.add_description(prompt());
  parser_.add_argument("file").help("input file").default_value("");
  parser_.add_argument("--onnx-file").help("ONNX file name").default_value("").nargs(1);

  DLINEAR_PARSE_PARAM_BOOL(parser_, csv, "--csv");
  DLINEAR_PARSE_PARAM_BOOL(parser_, continuous_output, "--continuous-output");
  DLINEAR_PARSE_PARAM_BOOL(parser_, complete, "-c", "--complete");
  DLINEAR_PARSE_PARAM_BOOL(parser_, debug_parsing, "--debug-parsing");
  DLINEAR_PARSE_PARAM_BOOL(parser_, debug_scanning, "--debug-scanning");
  DLINEAR_PARSE_PARAM_BOOL(parser_, disable_expansion, "--disable-expansion");
  DLINEAR_PARSE_PARAM_BOOL(parser_, enforce_check_sat, "--enforce-check-sat");
  DLINEAR_PARSE_PARAM_BOOL(parser_, optimize, "-o", "--optimize");
  DLINEAR_PARSE_PARAM_BOOL(parser_, produce_models, "-m", "--produce-models");
  DLINEAR_PARSE_PARAM_BOOL(parser_, skip_check_sat, "--skip-check-sat");
  DLINEAR_PARSE_PARAM_BOOL(parser_, silent, "-s", "--silent");
  DLINEAR_PARSE_PARAM_BOOL(parser_, with_timings, "-t", "--timings");
  DLINEAR_PARSE_PARAM_BOOL(parser_, read_from_stdin, "--in");
  DLINEAR_PARSE_PARAM_BOOL(parser_, verify, "--verify");

  //  DLINEAR_PARSE_PARAM_SCAN(parser_, number_of_jobs, 'i', unsigned int, "-j", "--jobs");
  DLINEAR_PARSE_PARAM_SCAN(parser_, precision, 'g', double, "-p", "--precision");
  DLINEAR_PARSE_PARAM_SCAN(parser_, random_seed, 'i', unsigned int, "-r", "--random-seed");
  DLINEAR_PARSE_PARAM_SCAN(parser_, simplex_sat_phase, 'i', int, "--simplex-sat-phase");
  DLINEAR_PARSE_PARAM_SCAN(parser_, verbose_simplex, 'i', int, "--verbose-simplex");

  parser_.add_argument("-V", "--verbose")
      .help("increase verbosity level. Can be used multiple times. Maximum verbosity level is 5 and default is 2")
      .action([this](const auto &) {
        if (verbosity_ < 5) ++verbosity_;
      })
      .append()
      .nargs(0);
  parser_.add_argument("-q", "--quiet")
      .help("decrease verbosity level. Can be used multiple times. Minimum verbosity level is 0 and default is 2")
      .action([this](const auto &) {
        if (verbosity_ > 0) --verbosity_;
      })
      .append()
      .nargs(0);

  DLINEAR_PARSE_PARAM_ENUM(
      parser_, lp_mode, "--lp-mode",
      "[ auto | pure-precision-boosting | pure-iterative-refinement | hybrid ] or [ 1 | 2 | 3 | 4 ]",
      if (value == "auto" || value == "1") return Config::LPMode::AUTO;
      if (value == "pure-precision-boosting" || value == "2") return Config::LPMode::PURE_PRECISION_BOOSTING;
      if (value == "pure-iterative-refinement" || value == "3") return Config::LPMode::PURE_ITERATIVE_REFINEMENT;
      if (value == "hybrid" || value == "4") return Config::LPMode::HYBRID;);
  DLINEAR_PARSE_PARAM_ENUM(parser_, format, "--format", "[ auto | smt2 | mps  | vnnlib ] or [ 1 | 2 | 3 | 4 ]",
                           if (value == "auto" || value == "1") return Config::Format::AUTO;
                           if (value == "smt2" || value == "2") return Config::Format::SMT2;
                           if (value == "mps" || value == "3") return Config::Format::MPS;
                           if (value == "vnnlib" || value == "4") return Config::Format::VNNLIB;);
  DLINEAR_PARSE_PARAM_ENUM(parser_, lp_solver, "--lp-solver", "[ soplex | qsoptex ] or [ 1 | 2 ]",
                           if (value == "soplex" || value == "1") return Config::LPSolver::SOPLEX;
                           if (value == "qsoptex" || value == "2") return Config::LPSolver::QSOPTEX;);
  DLINEAR_PARSE_PARAM_ENUM(parser_, sat_solver, "--sat-solver", "[ cadical | picosat ] or [ 1 | 2 ]",
                           if (value == "cadical" || value == "1") return Config::SatSolver::CADICAL;
                           if (value == "picosat" || value == "2") return Config::SatSolver::PICOSAT;);
  DLINEAR_PARSE_PARAM_ENUM(parser_, sat_default_phase, "--sat-default-phase",
                           "[ false | true | jeroslow-wang | random ] or [ 1 | 2 | 3 | 4 ]",
                           if (value == "false" || value == "1") return Config::SatDefaultPhase::False;
                           if (value == "true" || value == "2") return Config::SatDefaultPhase::True;
                           if (value == "jeroslow-wang" || value == "3") return Config::SatDefaultPhase::JeroslowWang;
                           if (value == "random" || value == "4") return Config::SatDefaultPhase::RandomInitialPhase;);
  DLINEAR_PARSE_PARAM_ENUM(
      parser_, bound_propagation_type, "--bound-propagation-type",
      "[ auto | eq-binomial | eq-polynomial | bound-polynomial ] or [ 1 | 2 | 3 | 4 ]",
      if (value == "auto" || value == "1") return Config::BoundPropagationType::AUTO;
      if (value == "eq-binomial" || value == "2") return Config::BoundPropagationType::EQ_BINOMIAL;
      if (value == "eq-polynomial" || value == "3") return Config::BoundPropagationType::EQ_POLYNOMIAL;
      if (value == "bound-polynomial" || value == "4") return Config::BoundPropagationType::BOUND_POLYNOMIAL;);
  DLINEAR_PARSE_PARAM_ENUM(
      parser_, bound_propagation_frequency, "--bound-propagation-frequency",
      "[ auto | never | on-fixed | on-iteration | always ] or [ 1 | 2 | 3 | 4 | 5 ]",
      if (value == "auto" || value == "1") return Config::PreprocessingRunningFrequency::AUTO;
      if (value == "never" || value == "2") return Config::PreprocessingRunningFrequency::NEVER;
      if (value == "on-fixed" || value == "3") return Config::PreprocessingRunningFrequency::ON_FIXED;
      if (value == "on-iteration" || value == "4") return Config::PreprocessingRunningFrequency::ON_ITERATION;
      if (value == "always" || value == "5") return Config::PreprocessingRunningFrequency::ALWAYS;);
  DLINEAR_PARSE_PARAM_ENUM(
      parser_, bound_implication_frequency, "--bound-implication-frequency",
      "[ auto | never | always ] or [ 1 | 2 | 3 ]",
      if (value == "auto" || value == "1") return Config::PreprocessingRunningFrequency::AUTO;
      if (value == "never" || value == "2") return Config::PreprocessingRunningFrequency::NEVER;
      if (value == "always" || value == "3") return Config::PreprocessingRunningFrequency::ALWAYS;);

  DLINEAR_TRACE("ArgParser::ArgParser: added all arguments");
}

std::ostream &operator<<(std::ostream &os, const ArgParser &parser) { return os << parser.parser_ << std::endl; }

Config ArgParser::toConfig() const {
  DLINEAR_TRACE("ArgParser::toConfig: converting to Config");
  Config config{};

  // Add all the options to the config in alphabetical order
  if (parser_.is_used("complete")) {
    config.m_complete().set_from_command_line(parser_.get<bool>("complete"));
    config.m_precision().set_from_command_line(0.0);
  }
  DLINEAR_PARAM_TO_CONFIG("bound-implication-frequency", bound_implication_frequency,
                          Config::PreprocessingRunningFrequency);
  DLINEAR_PARAM_TO_CONFIG("bound-propagation-frequency", bound_propagation_frequency,
                          Config::PreprocessingRunningFrequency);
  DLINEAR_PARAM_TO_CONFIG("csv", csv, bool);
  DLINEAR_PARAM_TO_CONFIG("continuous-output", continuous_output, bool);
  DLINEAR_PARAM_TO_CONFIG("debug-parsing", debug_parsing, bool);
  DLINEAR_PARAM_TO_CONFIG("debug-scanning", debug_scanning, bool);
  DLINEAR_PARAM_TO_CONFIG("disable-expansion", disable_expansion, bool);
  DLINEAR_PARAM_TO_CONFIG("bound-propagation-type", bound_propagation_type, Config::BoundPropagationType);
  DLINEAR_PARAM_TO_CONFIG("enforce-check-sat", enforce_check_sat, bool);
  config.m_filename().set_from_command_line(parser_.is_used("file") ? parser_.get<std::string>("file") : "");
  DLINEAR_PARAM_TO_CONFIG("format", format, Config::Format);
  DLINEAR_PARAM_TO_CONFIG("lp-mode", lp_mode, Config::LPMode);
  DLINEAR_PARAM_TO_CONFIG("lp-solver", lp_solver, Config::LPSolver);
  // DLINEAR_PARAM_TO_CONFIG("jobs", number_of_jobs, unsigned int);
  DLINEAR_PARAM_TO_CONFIG("onnx-file", onnx_file, std::string);
  DLINEAR_PARAM_TO_CONFIG("optimize", optimize, bool);
  DLINEAR_PARAM_TO_CONFIG("precision", precision, double);
  DLINEAR_PARAM_TO_CONFIG("produce-models", produce_models, bool);
  DLINEAR_PARAM_TO_CONFIG("random-seed", random_seed, unsigned int);
  DLINEAR_PARAM_TO_CONFIG("in", read_from_stdin, bool);
  DLINEAR_PARAM_TO_CONFIG("sat-default-phase", sat_default_phase, Config::SatDefaultPhase);
  DLINEAR_PARAM_TO_CONFIG("sat-solver", sat_solver, Config::SatSolver);
  DLINEAR_PARAM_TO_CONFIG("silent", silent, bool);
  DLINEAR_PARAM_TO_CONFIG("simplex-sat-phase", simplex_sat_phase, int);
  DLINEAR_PARAM_TO_CONFIG("skip-check-sat", skip_check_sat, bool);
  config.m_verbose_dlinear().set_from_command_line(verbosity_);
  DLINEAR_PARAM_TO_CONFIG("verbose-simplex", verbose_simplex, int);
  DLINEAR_PARAM_TO_CONFIG("verify", verify, bool);
  DLINEAR_PARAM_TO_CONFIG("timings", with_timings, bool);

  DLINEAR_TRACE_FMT("ArgParser::toConfig: {}", config);
  return config;
}

void ArgParser::validateOptions() {
  DLINEAR_TRACE("ArgParser::validateOptions: validating options");
  if (parser_.is_used("in") && parser_.is_used("file"))
    DLINEAR_INVALID_ARGUMENT("--in", "--in and file are mutually exclusive");
  if (!parser_.is_used("in") && !parser_.is_used("file"))
    DLINEAR_INVALID_ARGUMENT("file", "must be specified unless --in is used");
  if (parser_.is_used("in") && (parser_.get<Config::Format>("format") == Config::Format::AUTO))
    DLINEAR_INVALID_ARGUMENT("--in", "a format must be specified with --format");
  // Check file extension if a file is provided
  if (parser_.is_used("file")) {
    const Config::Format format = parser_.get<Config::Format>("format");
    const std::string extension{get_extension(parser_.get<std::string>("file"))};
    if (format == Config::Format::AUTO && extension != "smt2" && extension != "mps" && extension != "vnnlib") {
      DLINEAR_INVALID_ARGUMENT("file", "file must be .smt2, .mps or .vnnlib if --format is auto");
    }
    if (format == Config::Format::VNNLIB || (format == Config::Format::AUTO && extension == "vnnlib")) {
      if (!parser_.is_used("onnx-file"))
        DLINEAR_INVALID_ARGUMENT("--onnx-file", "must be provided with --format vnnlib");
      if (!std::filesystem::is_regular_file(parser_.get<std::string>("onnx-file")))
        DLINEAR_INVALID_ARGUMENT("--onnx-file", "cannot find file or the file is not a regular file");
    }
  }
  // Check if the file exists
  if (!parser_.is_used("in") && !std::filesystem::is_regular_file(parser_.get<std::string>("file")))
    DLINEAR_INVALID_ARGUMENT("file", "cannot find file or the file is not a regular file");
  if (parser_.is_used("precision") && parser_.is_used("complete"))
    DLINEAR_INVALID_ARGUMENT("--complete", "--complete and --precision are mutually exclusive");
  if (parser_.get<double>("precision") < 0) DLINEAR_INVALID_ARGUMENT("--precision", "cannot be negative");
  if (parser_.get<bool>("skip-check-sat") && parser_.get<bool>("produce-models"))
    DLINEAR_INVALID_ARGUMENT("--produce-models", "--produce-models and --skip-check-sat are mutually exclusive");
  if (parser_.is_used("verbose") && parser_.is_used("silent"))
    DLINEAR_INVALID_ARGUMENT("--verbose", "verbosity is forcefully set to 0 if --silent is provided");
  if (parser_.is_used("quiet") && parser_.is_used("silent"))
    DLINEAR_INVALID_ARGUMENT("--quiet", "verbosity is already set to 0 if --silent is provided");
  if (parser_.get<Config::LPSolver>("lp-solver") == Config::LPSolver::QSOPTEX)
    if (parser_.get<Config::LPMode>("lp-mode") != Config::LPMode::AUTO &&
        parser_.get<Config::LPMode>("lp-mode") != Config::LPMode::PURE_PRECISION_BOOSTING)
      DLINEAR_INVALID_ARGUMENT("--lp-solver", "QSopt_ex only supports 'auto' and 'pure-precision-boosting' modes");
  if (parser_.is_used("enforce-check-sat") && parser_.is_used("skip-check-sat"))
    DLINEAR_INVALID_ARGUMENT("--enforce-check-sat", "--enforce-check-sat and --skip-check-sat are mutually exclusive");
}

std::string ArgParser::version() { return DLINEAR_VERSION_STRING; }

std::string ArgParser::repositoryStatus() { return DLINEAR_VERSION_REPOSTAT; }

std::string ArgParser::prompt() const {
#ifndef NDEBUG
  const std::string build_type{"Debug"};
#else
  const std::string build_type{"Release"};
#endif
  std::string repo_stat = repositoryStatus();
  if (!repo_stat.empty()) {
    repo_stat = " (repository: " + repo_stat + ")";
  }

  std::string vstr = fmt::format("{} (v{}): delta-complete SMT solver ({} Build) {}", DLINEAR_PROGRAM_NAME, version(),
                                 build_type, repo_stat);
  if (!qsoptex_hash_.empty()) vstr += fmt::format(" (qsopt-ex: {})", qsoptex_hash_);
  if (!soplex_hash_.empty()) vstr += fmt::format(" (soplex: {})", soplex_hash_);
  return vstr;
}

}  // namespace dlinear
