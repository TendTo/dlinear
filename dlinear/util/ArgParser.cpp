/**
 * @file ArgParser.cpp
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 */
#include "ArgParser.h"

#include <utility>

#ifdef DLINEAR_ENABLED_QSOPTEX
#include "dlinear/libs/qsopt_ex.h"
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
#include "dlinear/libs/soplex.h"
#endif
#include "dlinear/util/exception.h"
#include "dlinear/util/filesystem.h"
#include "dlinear/util/logging.h"
#include "dlinear/version.h"

using std::cerr;
using std::endl;
using std::ostream;
using std::string;

namespace dlinear {

#define DLINEAR_PARSE_PARAM_BOOL(parser, name, ...)     \
  do {                                                  \
    parser.add_argument(__VA_ARGS__)                    \
        .help(dlinear::Config::help_##name)             \
        .default_value(dlinear::Config::default_##name) \
        .implicit_value(true);                          \
  } while (false)

#define DLINEAR_PARSE_PARAM_SCAN(parser, name, scan_char, scan_type, ...) \
  do {                                                                    \
    parser.add_argument(__VA_ARGS__)                                      \
        .help(dlinear::Config::help_##name)                               \
        .default_value(dlinear::Config::default_##name)                   \
        .scan<scan_char, scan_type>();                                    \
  } while (false)

ArgParser::ArgParser()
    : parser_{DLINEAR_PROGRAM_NAME, DLINEAR_VERSION_STRING},
#ifdef DLINEAR_ENABLED_QSOPTEX
      qsoptex_hash_{QSopt_ex_repository_status()},
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
      soplex_hash_{soplex::getGitHash()}
#endif
{
  DLINEAR_TRACE("ArgParser::ArgParser");
  addOptions();
}

void ArgParser::parse(int argc, const char **argv) {
  try {
    parser_.parse_args(argc, argv);
    DLINEAR_LOG_INIT_VERBOSITY((parser_.get<bool>("silent") ? 0 : parser_.get<int>("verbosity")));
    validateOptions();
    DLINEAR_TRACE("ArgParser::parse: parsed args");
  } catch (const std::runtime_error &err) {
    cerr << err.what() << endl;
    cerr << parser_;
    exit(EXIT_FAILURE);
  } catch (const std::invalid_argument &err) {
    cerr << err.what() << endl;
    cerr << parser_.usage() << endl;
    exit(EXIT_FAILURE);
  }
}

void ArgParser::addOptions() {
  DLINEAR_TRACE("ArgParser::addOptions: adding options");
  parser_.add_description(prompt());
  parser_.add_argument("file").help("input file").default_value("");

  DLINEAR_PARSE_PARAM_BOOL(parser_, continuous_output, "--continuous-output");
  DLINEAR_PARSE_PARAM_BOOL(parser_, debug_parsing, "--debug-parsing");
  DLINEAR_PARSE_PARAM_BOOL(parser_, debug_scanning, "--debug-scanning");
  DLINEAR_PARSE_PARAM_BOOL(parser_, use_polytope_in_forall, "--forall-polytope");
  DLINEAR_PARSE_PARAM_BOOL(parser_, produce_models, "-m", "--produce-models");
  DLINEAR_PARSE_PARAM_BOOL(parser_, use_polytope, "--polytope");
  DLINEAR_PARSE_PARAM_BOOL(parser_, use_worklist_fixpoint, "--worklist-fixpoint");
  DLINEAR_PARSE_PARAM_BOOL(parser_, skip_check_sat, "--skip-check-sat");
  DLINEAR_PARSE_PARAM_BOOL(parser_, silent, "-s", "--silent");
  DLINEAR_PARSE_PARAM_BOOL(parser_, with_timings, "-t", "--timings");
  DLINEAR_PARSE_PARAM_BOOL(parser_, read_from_stdin, "--in");
  DLINEAR_PARSE_PARAM_BOOL(parser_, use_local_optimization, "--local-optimization");

  DLINEAR_PARSE_PARAM_SCAN(parser_, number_of_jobs, 'i', uint, "-j", "--jobs");
  DLINEAR_PARSE_PARAM_SCAN(parser_, nlopt_ftol_abs, 'g', double, "--nlopt-ftol-abs");
  DLINEAR_PARSE_PARAM_SCAN(parser_, nlopt_ftol_rel, 'g', double, "--nlopt-ftol-rel");
  DLINEAR_PARSE_PARAM_SCAN(parser_, nlopt_maxeval, 'i', uint, "--nlopt-maxeval");
  DLINEAR_PARSE_PARAM_SCAN(parser_, nlopt_maxtime, 'g', double, "--nlopt-maxtime");
  DLINEAR_PARSE_PARAM_SCAN(parser_, precision, 'g', double, "-p", "--precision");
  DLINEAR_PARSE_PARAM_SCAN(parser_, random_seed, 'i', uint, "-r", "--random-seed");
  DLINEAR_PARSE_PARAM_SCAN(parser_, simplex_sat_phase, 'i', int, "--simplex-sat-phase");
  DLINEAR_PARSE_PARAM_SCAN(parser_, verbose_dlinear, 'i', int, "--verbosity");
  DLINEAR_PARSE_PARAM_SCAN(parser_, verbose_simplex, 'i', int, "--verbose-simplex");

  parser_.add_argument("--format")
      .help(Config::help_format)
      .default_value(Config::default_format)
      .action([](const std::string &value) {
        if (value == "auto") return Config::Format::AUTO;
        if (value == "smt2") return Config::Format::SMT2;
        if (value == "mps") return Config::Format::MPS;
        DLINEAR_INVALID_ARGUMENT("--format", value);
      });
  parser_.add_argument("--lp-solver")
      .help(Config::help_lp_solver)
      .default_value(Config::default_lp_solver)
      .action([](const std::string &value) {
        if (value == "soplex" || value == "1") return Config::LPSolver::SOPLEX;
        if (value == "qsoptex" || value == "2") return Config::LPSolver::QSOPTEX;
        DLINEAR_INVALID_ARGUMENT("--lp-solver", value);
      });
  parser_.add_argument("--lp-mode")
      .help(Config::help_lp_mode)
      .default_value(Config::default_lp_mode)
      .action([](const std::string &value) {
        if (value == "auto" || value == "0") return Config::LPMode::AUTO;
        if (value == "pure-precision-boosting" || value == "1") return Config::LPMode::PURE_PRECISION_BOOSTING;
        if (value == "pure-iterative-refinement" || value == "2") return Config::LPMode::PURE_ITERATIVE_REFINEMENT;
        if (value == "hybrid" || value == "3") return Config::LPMode::HYBRID;
        DLINEAR_INVALID_ARGUMENT("--lp-mode", value);
      });
  parser_.add_argument("--sat-default-phase")
      .help(Config::help_sat_default_phase)
      .default_value(Config::default_sat_default_phase)
      .action([](const string &value) {
        int v = std::stoi(value);
        if (v == 0) return Config::SatDefaultPhase::False;
        if (v == 1) return Config::SatDefaultPhase::True;
        if (v == 2) return Config::SatDefaultPhase::JeroslowWang;
        if (v == 3) return Config::SatDefaultPhase::RandomInitialPhase;
        DLINEAR_INVALID_ARGUMENT("--sat-default-phase", value);
      });

  DLINEAR_TRACE("ArgParser::ArgParser: added all arguments");
}

ostream &operator<<(ostream &os, const ArgParser &parser) {
  os << parser.parser_ << endl;
  return os;
}

Config ArgParser::toConfig() const {
  DLINEAR_TRACE("ArgParser::toConfig: converting to Config");
  Config config{};

  config.m_filename().set_from_command_line(parser_.is_used("file") ? parser_.get<string>("file") : "");

  // Add all the options to the config in alphabetical order
  if (parser_.is_used("continuous-output"))
    config.m_continuous_output().set_from_command_line(parser_.get<bool>("continuous-output"));
  if (parser_.is_used("debug-parsing"))
    config.m_debug_parsing().set_from_command_line(parser_.get<bool>("debug-parsing"));
  if (parser_.is_used("debug-scanning")) config.m_debug_scanning().set_from_command_line(true);
  if (parser_.is_used("format")) config.m_format().set_from_command_line(parser_.get<Config::Format>("format"));
  if (parser_.is_used("forall-polytope"))
    config.m_use_polytope_in_forall().set_from_command_line(parser_.get<bool>("forall-polytope"));
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
    config.m_nlopt_maxeval().set_from_command_line(parser_.get<uint>("nlopt-maxeval"));
  if (parser_.is_used("nlopt-maxtime"))
    config.m_nlopt_maxtime().set_from_command_line(parser_.get<double>("nlopt-maxtime"));
  if (parser_.is_used("polytope")) config.m_use_polytope().set_from_command_line(parser_.get<bool>("polytope"));
  if (parser_.is_used("precision")) config.m_precision().set_from_command_line(parser_.get<double>("precision"));
  if (parser_.is_used("produce-models"))
    config.m_produce_models().set_from_command_line(parser_.get<bool>("produce-models"));
  if (parser_.is_used("random-seed")) config.m_random_seed().set_from_command_line(parser_.get<uint>("random-seed"));
  if (parser_.is_used("sat-default-phase"))
    config.m_sat_default_phase().set_from_command_line(parser_.get<Config::SatDefaultPhase>("sat-default-phase"));
  if (parser_.is_used("simplex-sat-phase"))
    config.m_simplex_sat_phase().set_from_command_line(parser_.get<int>("simplex-sat-phase"));
  if (parser_.is_used("silent")) config.m_silent().set_from_command_line(parser_.get<bool>("silent"));
  if (parser_.is_used("skip-check-sat"))
    config.m_skip_check_sat().set_from_command_line(parser_.get<bool>("skip-check-sat"));
  if (parser_.is_used("timings")) config.m_with_timings().set_from_command_line(parser_.get<bool>("timings"));
  if (parser_.is_used("verbosity")) config.m_verbose_dlinear().set_from_command_line(parser_.get<int>("verbosity"));
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
    DLINEAR_INVALID_ARGUMENT("--in", "cannot be set if file is specified");
  if (!parser_.is_used("in") && !parser_.is_used("file"))
    DLINEAR_INVALID_ARGUMENT("file", "must be specified if --in is not used");
  // Check file extension
  Config::Format format = parser_.get<Config::Format>("format");
  string extension{get_extension(parser_.get<string>("file"))};
  if (format == Config::Format::AUTO && extension != "smt2" && extension != "mps") {
    DLINEAR_INVALID_ARGUMENT("file", "file must be .smt2 or .mps if --format is auto");
  } else if ((format == Config::Format::SMT2 && extension != "smt2") ||
             (format == Config::Format::MPS && extension != "mps")) {
    DLINEAR_INVALID_ARGUMENT("file", "the file extension does not match the format");
  }
  if (!parser_.get<bool>("in") && !file_exists(parser_.get<string>("file")))
    DLINEAR_INVALID_ARGUMENT("file", "cannot find file");
  if (parser_.get<double>("precision") < 0) DLINEAR_INVALID_ARGUMENT("--precision", "cannot be negative");
  if (parser_.get<bool>("skip-check-sat") && parser_.get<bool>("produce-models"))
    DLINEAR_INVALID_ARGUMENT("--produce-models", "no models will be produced if --skip-check-sat is provided");
  if (parser_.is_used("verbosity") && parser_.is_used("silent"))
    DLINEAR_INVALID_ARGUMENT("--verbosity", "verbosity is set to 0 if --silent is provided");
  if (parser_.get<Config::LPSolver>("lp-solver") == Config::LPSolver::QSOPTEX)
    if (parser_.get<Config::LPMode>("lp-mode") != Config::LPMode::AUTO &&
        parser_.get<Config::LPMode>("lp-mode") != Config::LPMode::PURE_PRECISION_BOOSTING)
      DLINEAR_INVALID_ARGUMENT("--lp-solver", "QSopt_ex only supports 'auto' and 'pure-precision-boosting' modes");
}

string ArgParser::version() const { return DLINEAR_VERSION_STRING; }

string ArgParser::repositoryStatus() const { return DLINEAR_VERSION_REPOSTAT; }

string ArgParser::prompt() const {
#ifndef NDEBUG
  const string build_type{"Debug"};
#else
  const string build_type{"Release"};
#endif
  string repo_stat = repositoryStatus();
  if (!repo_stat.empty()) {
    repo_stat = " (repository: " + repo_stat + ")";
  }

  string vstr = fmt::format("{} (v{}): delta-complete SMT solver ({} Build) {}", DLINEAR_PROGRAM_NAME, version(),
                            build_type, repo_stat);
  if (!qsoptex_hash_.empty()) vstr += fmt::format(" (qsopt-ex: {})", qsoptex_hash_);
  if (!soplex_hash_.empty()) vstr += fmt::format(" (soplex: {})", soplex_hash_);
  return vstr;
}

}  // namespace dlinear
