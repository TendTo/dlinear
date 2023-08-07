/**
 * @file ArgParser.cpp
 * @author tend
 * @date 07 Aug 2023
 * @copyright 2023 tend
 */
#include "ArgParser.h"

namespace dlinear {
ArgParser::ArgParser() : parser_{DLINEAR_NAME, DLINEAR_VERSION} {
  DLINEAR_TRACE("ArgParser::ArgParser");
  addOptions();
}

void ArgParser::parse(int argc, const char **argv) {
  try {
    parser_.parse_args(argc, argv);
    DLINEAR_LOG_INIT(DLINEAR_VERBOSITY_TO_LOG_LEVEL(parser_.get<int>("verbosity")));
  }
  catch (const std::runtime_error &err) {
    cerr << err.what() << endl;
    cerr << parser_;
    exit(EXIT_FAILURE);
  }
}

void ArgParser::addOptions() {
  parser_.add_argument("--verbosity")
      .help(
          "set verbosity level."
          "0 for critical, 1 for error, 2 for warn, 3 for info, 4 for debug, 5 for trace."
          "Any other value will disable logging.")
      .default_value(0)
      .action([](const string &value) { return std::stoi(value); });
  parser_.add_argument("-p", "--precision")
      .help("set the precision of the solver")
      .default_value(1e-6)
      .action([](const string &value) { return std::stod(value); });
  parser_.add_argument("-m", "--produce-models")
      .help("produce models")
      .default_value(false)
      .implicit_value(true);
  parser_.add_argument("-r", "--random-seed")
      .help("set the random seed")
      .default_value(0ul)
      .action([](const string &value) { return std::stoul(value); });
}

ostream &operator<<(ostream &os, const ArgParser &parser) {
  os << parser.parser_ << endl;
  return os;
}

Config ArgParser::toConfig() const {
  Config config{};
  config.setVerbosity(parser_.get<int>("verbosity"));
  config.setPrecision(parser_.get<double>("precision"));
  config.setProduceModels(parser_.get<bool>("produce-models"));
  config.setRandomSeed(parser_.get<u_int64_t>("random-seed"));
  DLINEAR_TRACE_FMT("ArgParser::toConfig() -> {}", config);
  return config;
}

} // namespace dlinear
