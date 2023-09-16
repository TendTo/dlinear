/**
 * @file ArgParser.cpp
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 */
#include "ArgParser.h"

#include <utility>

#include "dlinear/util/exception.h"
#include "dlinear/util/filesystem.h"
#include "dlinear/util/logging.h"
#include "dlinear/version.h"

using std::cerr;
using std::endl;
using std::ostream;
using std::string;

namespace dlinear {
ArgParser::ArgParser() : parser_{DLINEAR_PROGRAM_NAME, DLINEAR_VERSION_STRING} {
  DLINEAR_TRACE("ArgParser::ArgParser");
  addOptions();
}

ArgParser::ArgParser(string qsopt_exHash, string soplexHash)
    : parser_{DLINEAR_PROGRAM_NAME, DLINEAR_VERSION_STRING},
      qsoptex_hash_{std::move(qsopt_exHash)},
      soplex_hash_{std::move(soplexHash)} {
  DLINEAR_TRACE("ArgParser::ArgParser");
  addOptions();
}

void ArgParser::parse(int argc, const char **argv) {
  try {
    parser_.parse_args(argc, argv);
    DLINEAR_LOG_INIT_VERBOSITY(parser_.get<int>("verbosity"));
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
  parser_.add_argument("-j", "--jobs")
      .help("set the number of jobs")
      .default_value(DLINEAR_DEFAULT_NUMBER_OF_JOBS)
      .scan<'i', uint>();
  parser_.add_argument("--continuous-output")
      .help("report partial results continuously, as and when available")
      .default_value(DLINEAR_DEFAULT_CONTINUOUS_OUTPUT)
      .implicit_value(true);
  parser_.add_argument("--debug-parsing")
      .help("debug parsing")
      .default_value(DLINEAR_DEFAULT_DEBUG_PARSING)
      .implicit_value(true);
  parser_.add_argument("--debug-scanning")
      .help("debug scanning/lexing")
      .default_value(DLINEAR_DEFAULT_DEBUG_SCANNING)
      .implicit_value(true);
  parser_.add_argument("--exhaustive")
      .help(
          "run the algorithm to completion, by setting the precision to 0"
          " This may not solve the problem exactly in all cases;"
          " try --precision 0 for an explanation.")
      .default_value(DLINEAR_DEFAULT_EXHAUSTIVE)
      .implicit_value(true);
  parser_.add_argument("--forall-polytope")
      .help("use polytope contractor in forall contractor")
      .default_value(DLINEAR_DEFAULT_USE_POLYTOPE_IN_FORALL)
      .implicit_value(true);
  parser_.add_argument("--format")
      .help("file format. Any one of these: smt2, auto (use file extension)")
      .default_value(string{"auto"})  // TODO: check config
      .action([](const std::string &value) {
        if (value != "smt2" && value != "auto") DLINEAR_INVALID_ARGUMENT("--format", value);
        return value;
      });
  parser_.add_argument("--in")
      .help("read from standard input. Uses smt2 by default.")
      .default_value(false)  // TODO: check
      .implicit_value(true);
  parser_.add_argument("--local-optimization")
      .help("use local optimization algorithm for exist-forall problems")
      .default_value(DLINEAR_DEFAULT_USE_LOCAL_OPTIMIZATION)
      .implicit_value(true);
  parser_.add_argument("--lp-solver")
      .help("set the LP solver. One of: soplex (or 1), qsoptex (or 2)")
      .default_value(Config::LPSolver::QSOPTEX)
      .action([](const std::string &value) {
        if (value == "soplex" || value == "1") return Config::LPSolver::SOPLEX;
        if (value == "qsoptex" || value == "2") return Config::LPSolver::QSOPTEX;
        DLINEAR_INVALID_ARGUMENT("--lp-solver", value);
      });
  parser_.add_argument("-m", "--produce-models")
      .help("produce models")
      .default_value(DLINEAR_DEFAULT_PRODUCE_MODELS)
      .implicit_value(true);
  parser_.add_argument("--nlopt-ftol-abs")
      .help("set the absolute tolerance on function value")
      .default_value(DLINEAR_DEFAULT_NLOPTF_TO_ABS)
      .scan<'g', double>();
  parser_.add_argument("--nlopt-ftol-rel")
      .help("set the relative tolerance on function value")
      .default_value(DLINEAR_DEFAULT_NLOPTF_TO_REL)
      .scan<'g', double>();
  parser_.add_argument("--nlopt-maxeval")
      .help("set the maximum number of function evaluations")
      .default_value(DLINEAR_DEFAULT_NLOPT_MAX_EVAL)
      .scan<'i', uint>();
  parser_.add_argument("--nlopt-maxtime")
      .help("set the maximum optimization time (in second)")
      .default_value(DLINEAR_DEFAULT_NLOPT_MAX_TIME)
      .scan<'g', double>();
  parser_.add_argument("--polytope")
      .help("use polytope contractor")
      .default_value(DLINEAR_DEFAULT_USE_POLYTOPE)
      .implicit_value(true);
  parser_.add_argument("-p", "--precision")
      .help("set the precision of the solver")
      .default_value(DLINEAR_DEFAULT_PRECISION)
      .scan<'g', double>();
  parser_.add_argument("-r", "--random-seed")
      .help("set the random seed")
      .default_value(DLINEAR_DEFAULT_RANDOM_SEED)
      .scan<'i', uint>();
  parser_.add_argument("--sat-default-phase")
      .help(
          "set default initial phase for SAT solver.\n"
          "\t\t\t0 = false\n"
          "\t\t\t1 = true\n"
          "\t\t\t2 = Jeroslow-Wang\n"
          "\t\t\t3 = random initial phase\n\t\t\t")
      .default_value(DLINEAR_DEFAULT_SAT_PHASE)
      .action([](const string &value) {
        int v = std::stoi(value);
        switch (v) {
          case 0:
            return Config::SatDefaultPhase::False;
          case 1:
            return Config::SatDefaultPhase::True;
          case 2:
            return Config::SatDefaultPhase::JeroslowWang;
          case 3:
            return Config::SatDefaultPhase::RandomInitialPhase;
          default:
            DLINEAR_INVALID_ARGUMENT("--sat-default-phase", value);
        }
      });
  parser_.add_argument("--simplex-sat-phase")
      .help("set default initial phase for simplex. Either 1 or 2")
      .default_value(DLINEAR_DEFAULT_SIMPLEX_SAT_PHASE)
      .action([](const string &value) {
        int v = std::stoi(value);
        if (v != 1 && v != 2) DLINEAR_INVALID_ARGUMENT("--simplex-sat-phase", value);
        return v;
      });
  parser_.add_argument("-t", "--timings")
      .help("report timings alongside results")
      .default_value(DLINEAR_DEFAULT_WITH_TIMINGS)
      .implicit_value(true);
  parser_.add_argument("--verbosity")
      .help(
          "set verbosity level."
          "0 for critical, 1 for error, 2 for warn, 3 for info, 4 for debug, 5 for trace."
          "Any other value will disable logging.")
      .default_value(DLINEAR_DEFAULT_VERBOSE_DLINEAR)
      .scan<'i', int>();
  parser_.add_argument("--verbose-simplex")
      .help("set the verbosity level for simplex. In the range [0, 5]")
      .default_value(DLINEAR_DEFAULT_VERBOSE_SIMPLEX)
      .action([](const std::string &value) {
        int level = std::stoi(value);
        if (level < 0 || level > 5) DLINEAR_INVALID_ARGUMENT("--sat-default-phase", value);
        return level;
      });
  parser_.add_argument("--worklist-fixpoint")
      .help("use worklist fixpoint algorithm in ICP")
      .default_value(DLINEAR_DEFAULT_USE_WORKLIST_FIXPOINT)
      .implicit_value(true);
  DLINEAR_TRACE("ArgParser::ArgParser: added all arguments");
}

ostream &operator<<(ostream &os, const ArgParser &parser) {
  os << parser.parser_ << endl;
  return os;
}

Config ArgParser::toConfig() const {
  DLINEAR_TRACE("ArgParser::toConfig: converting to Config");
  Config config{};
  config.mutable_filename().set_from_command_line(parser_.is_used("file") ? parser_.get<string>("file") : "");
  if (parser_.is_used("in")) config.mutable_read_from_stdin().set_from_command_line(parser_.get<bool>("in"));
  if (parser_.is_used("precision")) config.mutable_precision().set_from_command_line(parser_.get<double>("precision"));
  if (parser_.is_used("produce-models"))
    config.mutable_produce_models().set_from_command_line(parser_.get<bool>("produce-models"));
  if (parser_.is_used("verbosity"))
    config.mutable_verbose_dlinear().set_from_command_line(parser_.get<int>("verbosity"));
  if (parser_.is_used("jobs")) config.mutable_number_of_jobs().set_from_command_line(parser_.get<uint>("jobs"));
  if (parser_.is_used("timings")) config.mutable_with_timings().set_from_command_line(parser_.get<bool>("timings"));
  if (parser_.is_used("continuous-output"))
    config.mutable_continuous_output().set_from_command_line(parser_.get<bool>("continuous-output"));
  if (parser_.is_used("random-seed"))
    config.mutable_random_seed().set_from_command_line(parser_.get<uint>("random-seed"));
  if (parser_.is_used("lp-solver"))
    config.mutable_lp_solver().set_from_command_line(parser_.get<Config::LPSolver>("lp-solver"));
  if (parser_.is_used("verbose-simplex"))
    config.mutable_verbose_simplex().set_from_command_line(parser_.get<int>("verbose-simplex"));
  if (parser_.is_used("nlopt-ftol-rel"))
    config.mutable_nlopt_ftol_rel().set_from_command_line(parser_.get<double>("nlopt-ftol-rel"));
  if (parser_.is_used("nlopt-ftol-abs"))
    config.mutable_nlopt_ftol_abs().set_from_command_line(parser_.get<double>("nlopt-ftol-abs"));
  if (parser_.is_used("nlopt-maxeval"))
    config.mutable_nlopt_maxeval().set_from_command_line(parser_.get<uint>("nlopt-maxeval"));
  if (parser_.is_used("nlopt-maxtime"))
    config.mutable_nlopt_maxtime().set_from_command_line(parser_.get<double>("nlopt-maxtime"));
  if (parser_.is_used("sat-default-phase"))
    config.mutable_sat_default_phase().set_from_command_line(parser_.get<Config::SatDefaultPhase>("sat-default-phase"));
  if (parser_.is_used("simplex-sat-phase"))
    config.mutable_simplex_sat_phase().set_from_command_line(parser_.get<int>("simplex-sat-phase"));
  if (parser_.is_used("worklist-fixpoint"))
    config.mutable_use_worklist_fixpoint().set_from_command_line(parser_.get<bool>("worklist-fixpoint"));
  if (parser_.is_used("local-optimization"))
    config.mutable_use_local_optimization().set_from_command_line(parser_.get<bool>("local-optimization"));
  if (parser_.is_used("debug-scanning"))
    config.mutable_debug_scanning().set_from_command_line(parser_.get<bool>("debug-scanning"));
  if (parser_.is_used("debug-parsing"))
    config.mutable_debug_parsing().set_from_command_line(parser_.get<bool>("debug-parsing"));
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
  string format = parser_.get<string>("format");
  string extension{get_extension(parser_.get<string>("file"))};
  if (format == "auto" && extension != "smt2") {
    DLINEAR_INVALID_ARGUMENT("file", "file must be .smt2 if --format is auto");
  } else if (format != "auto" && format != extension) {
    DLINEAR_INVALID_ARGUMENT("file", "the file extension does not match the format");
  }
  if (!file_exists(parser_.get<string>("file"))) DLINEAR_INVALID_ARGUMENT("file", "cannot find file");
  if (parser_.is_used("exhaustive") && parser_.is_used("precision"))
    DLINEAR_INVALID_ARGUMENT("--exhaustive", "cannot be set if --precision is used");
  if (parser_.get<double>("precision") == 0)
    DLINEAR_INVALID_ARGUMENT("--precision",
                             "cannot be set to zero. Use --exhaustive instead."
                             "\n"
                             "In order to support problems that may contain strict inequalities, dLinear4"
                             "reduces the precision value (or delta) by a small amount, and any strict"
                             "inequalities are de-strictified before being sent to the simplex solver. For"
                             "this reason, the precision must be strictly positive."
                             "\n"
                             "If you are sure that your problem contains no strict inequalities (not just in"
                             "the asserted formulas themselves, but in any conjunctive clause derived from"
                             "them), or if you simply wish to run the algorithm to completion, use"
                             "--exhaustive instead, and the precision value will be set to zero (but strict"
                             "inequalities will still be de-strictified)."
                             "\n"
                             "Hint: try --exhaustive in conjunction with --continuous-output "
                             "to find all delta-sat thresholds.");
  if (parser_.get<double>("precision") < 0) DLINEAR_INVALID_ARGUMENT("--precision", "cannot be negative");
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
