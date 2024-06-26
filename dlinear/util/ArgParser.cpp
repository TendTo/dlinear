/**
 * @file ArgParser.cpp
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 */
// IWYU pragma: no_include "argparse/argparse.hpp" // Already included in the header
#include "ArgParser.h"

#include <cstdlib>
#include <filesystem>
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

  DLINEAR_PARSE_PARAM_BOOL(parser_, continuous_output, "--continuous-output");
  DLINEAR_PARSE_PARAM_BOOL(parser_, complete, "-c", "--complete");
  DLINEAR_PARSE_PARAM_BOOL(parser_, debug_parsing, "--debug-parsing");
  DLINEAR_PARSE_PARAM_BOOL(parser_, debug_scanning, "--debug-scanning");
  DLINEAR_PARSE_PARAM_BOOL(parser_, disable_theory_preprocessor, "--disable-theory-preprocessor");
  DLINEAR_PARSE_PARAM_BOOL(parser_, enforce_check_sat, "--enforce-check-sat");
  DLINEAR_PARSE_PARAM_BOOL(parser_, optimize, "-o", "--optimize");
  DLINEAR_PARSE_PARAM_BOOL(parser_, produce_models, "-m", "--produce-models");
  DLINEAR_PARSE_PARAM_BOOL(parser_, use_polytope, "--polytope");
  DLINEAR_PARSE_PARAM_BOOL(parser_, use_worklist_fixpoint, "--worklist-fixpoint");
  DLINEAR_PARSE_PARAM_BOOL(parser_, skip_check_sat, "--skip-check-sat");
  DLINEAR_PARSE_PARAM_BOOL(parser_, silent, "-s", "--silent");
  DLINEAR_PARSE_PARAM_BOOL(parser_, with_timings, "-t", "--timings");
  DLINEAR_PARSE_PARAM_BOOL(parser_, read_from_stdin, "--in");
  DLINEAR_PARSE_PARAM_BOOL(parser_, use_local_optimization, "--local-optimization");
  DLINEAR_PARSE_PARAM_BOOL(parser_, use_polytope_in_forall, "--forall-polytope");

  DLINEAR_PARSE_PARAM_SCAN(parser_, number_of_jobs, 'i', unsigned int, "-j", "--jobs");
  DLINEAR_PARSE_PARAM_SCAN(parser_, nlopt_ftol_abs, 'g', double, "--nlopt-ftol-abs");
  DLINEAR_PARSE_PARAM_SCAN(parser_, nlopt_ftol_rel, 'g', double, "--nlopt-ftol-rel");
  DLINEAR_PARSE_PARAM_SCAN(parser_, nlopt_maxeval, 'i', unsigned int, "--nlopt-maxeval");
  DLINEAR_PARSE_PARAM_SCAN(parser_, nlopt_maxtime, 'g', double, "--nlopt-maxtime");
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

  parser_.add_argument("--format")
      .help(Config::help_format)
      .nargs(1)
      .default_value(Config::default_format)
      .action([](const std::string &value) {
        if (value == "auto" || value == "1") return Config::Format::AUTO;
        if (value == "smt2" || value == "2") return Config::Format::SMT2;
        if (value == "mps" || value == "3") return Config::Format::MPS;
        DLINEAR_INVALID_ARGUMENT_EXPECTED("--format", value, "[ auto | smt2 | mps ] or [ 1 | 2 | 3 ]");
      })
      .nargs(1);
  parser_.add_argument("--lp-solver")
      .help(Config::help_lp_solver)
      .default_value(Config::default_lp_solver)
      .action([](const std::string &value) {
        if (value == "soplex" || value == "1") return Config::LPSolver::SOPLEX;
        if (value == "qsoptex" || value == "2") return Config::LPSolver::QSOPTEX;
        DLINEAR_INVALID_ARGUMENT_EXPECTED("--lp-solver", value, "[ soplex | qsoptex ] or [ 1 | 2 ]");
      })
      .nargs(1);
  parser_.add_argument("--lp-mode")
      .help(Config::help_lp_mode)
      .default_value(Config::default_lp_mode)
      .action([](const std::string &value) {
        if (value == "auto" || value == "1") return Config::LPMode::AUTO;
        if (value == "pure-precision-boosting" || value == "2") return Config::LPMode::PURE_PRECISION_BOOSTING;
        if (value == "pure-iterative-refinement" || value == "3") return Config::LPMode::PURE_ITERATIVE_REFINEMENT;
        if (value == "hybrid" || value == "4") return Config::LPMode::HYBRID;
        DLINEAR_INVALID_ARGUMENT_EXPECTED(
            "--lp-mode", value,
            "[ auto | pure-precision-boosting | pure-iterative-refinement | hybrid ] or [ 1 | 2 | 3 | 4 ]");
      })
      .nargs(1);
  parser_.add_argument("--sat-default-phase")
      .help(Config::help_sat_default_phase)
      .default_value(Config::default_sat_default_phase)
      .action([](const std::string &value) {
        if (value == "false" || value == "1") return Config::SatDefaultPhase::False;
        if (value == "true" || value == "2") return Config::SatDefaultPhase::True;
        if (value == "jeroslow-wang" || value == "3") return Config::SatDefaultPhase::JeroslowWang;
        if (value == "random" || value == "4") return Config::SatDefaultPhase::RandomInitialPhase;
        DLINEAR_INVALID_ARGUMENT_EXPECTED("--sat-default-phase", value,
                                          "[ false | true | jeroslow-wang | random ] or [ 1 | 2 | 3 | 4 ]");
      })
      .nargs(1);

  DLINEAR_TRACE("ArgParser::ArgParser: added all arguments");
}

std::ostream &operator<<(std::ostream &os, const ArgParser &parser) { return os << parser.parser_ << std::endl; }

Config ArgParser::toConfig() const {
  DLINEAR_TRACE("ArgParser::toConfig: converting to Config");
  Config config{};

  config.m_filename().set_from_command_line(parser_.is_used("file") ? parser_.get<std::string>("file") : "");

  // Add all the options to the config in alphabetical order
  if (parser_.is_used("complete")) {
    config.m_complete().set_from_command_line(parser_.get<bool>("complete"));
    config.m_precision().set_from_command_line(0.0);
  }
  if (parser_.is_used("continuous-output"))
    config.m_continuous_output().set_from_command_line(parser_.get<bool>("continuous-output"));
  if (parser_.is_used("debug-parsing"))
    config.m_debug_parsing().set_from_command_line(parser_.get<bool>("debug-parsing"));
  if (parser_.is_used("debug-scanning"))
    config.m_debug_scanning().set_from_command_line(parser_.get<bool>("debug-scanning"));
  if (parser_.is_used("disable-theory-preprocessor"))
    config.m_disable_theory_preprocessor().set_from_command_line(parser_.get<bool>("disable-theory-preprocessor"));
  if (parser_.is_used("format")) config.m_format().set_from_command_line(parser_.get<Config::Format>("format"));
  if (parser_.is_used("forall-polytope"))
    config.m_use_polytope_in_forall().set_from_command_line(parser_.get<bool>("forall-polytope"));
  if (parser_.is_used("in")) config.m_read_from_stdin().set_from_command_line(parser_.get<bool>("in"));
  if (parser_.is_used("lp-solver"))
    config.m_lp_solver().set_from_command_line(parser_.get<Config::LPSolver>("lp-solver"));
  if (parser_.is_used("lp-mode")) config.m_lp_mode().set_from_command_line(parser_.get<Config::LPMode>("lp-mode"));
  if (parser_.is_used("produce-models"))
    config.m_produce_models().set_from_command_line(parser_.get<bool>("produce-models"));
  if (parser_.is_used("nlopt-ftol-abs"))
    config.m_nlopt_ftol_abs().set_from_command_line(parser_.get<double>("nlopt-ftol-abs"));
  if (parser_.is_used("nlopt-ftol-rel"))
    config.m_nlopt_ftol_rel().set_from_command_line(parser_.get<double>("nlopt-ftol-rel"));
  if (parser_.is_used("nlopt-maxeval"))
    config.m_nlopt_maxeval().set_from_command_line(parser_.get<unsigned int>("nlopt-maxeval"));
  if (parser_.is_used("nlopt-maxtime"))
    config.m_nlopt_maxtime().set_from_command_line(parser_.get<double>("nlopt-maxtime"));
  if (parser_.is_used("optimize")) config.m_optimize().set_from_command_line(parser_.get<bool>("optimize"));
  if (parser_.is_used("polytope")) config.m_use_polytope().set_from_command_line(parser_.get<bool>("polytope"));
  if (parser_.is_used("precision")) config.m_precision().set_from_command_line(parser_.get<double>("precision"));
  if (parser_.is_used("produce-models"))
    config.m_produce_models().set_from_command_line(parser_.get<bool>("produce-models"));
  if (parser_.is_used("random-seed"))
    config.m_random_seed().set_from_command_line(parser_.get<unsigned int>("random-seed"));
  if (parser_.is_used("sat-default-phase"))
    config.m_sat_default_phase().set_from_command_line(parser_.get<Config::SatDefaultPhase>("sat-default-phase"));
  if (parser_.is_used("simplex-sat-phase"))
    config.m_simplex_sat_phase().set_from_command_line(parser_.get<int>("simplex-sat-phase"));
  if (parser_.is_used("silent")) config.m_silent().set_from_command_line(parser_.get<bool>("silent"));
  if (parser_.is_used("skip-check-sat"))
    config.m_skip_check_sat().set_from_command_line(parser_.get<bool>("skip-check-sat"));
  if (parser_.is_used("enforce-check-sat"))
    config.m_enforce_check_sat().set_from_command_line(parser_.get<bool>("enforce-check-sat"));
  if (parser_.is_used("timings")) config.m_with_timings().set_from_command_line(parser_.get<bool>("timings"));
  if (parser_.is_used("verbose") || parser_.is_used("quiet"))
    config.m_verbose_dlinear().set_from_command_line(verbosity_);
  if (parser_.is_used("verbose-simplex"))
    config.m_verbose_simplex().set_from_command_line(parser_.get<int>("verbose-simplex"));
  if (parser_.is_used("worklist-fixpoint"))
    config.m_use_worklist_fixpoint().set_from_command_line(parser_.get<bool>("worklist-fixpoint"));

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
    if (format == Config::Format::AUTO && extension != "smt2" && extension != "mps") {
      DLINEAR_INVALID_ARGUMENT("file", "file must be .smt2 or .mps if --format is auto");
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
