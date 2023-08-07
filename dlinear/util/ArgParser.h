/**
 * @file ArgParser.h
 * @author tend
 * @date 07 Aug 2023
 * @copyright 2023 tend
 * @brief ArgParser class.
 * Used to parse command line arguments.
 *
 * Parse the command line arguments and convert them to Config.
 * The config object will then be used throughout the program.
 * The default values are defined in the configuration of the parser.
 */
#ifndef DLINEAR5_ARGPARSER_H
#define DLINEAR5_ARGPARSER_H

#include <iostream>
#include <string>
#include <argparse/argparse.hpp>
#include "dlinear/util/Config.h"
#include "dlinear/util/logging.h"

#ifndef DLINEAR_NAME
#define DLINEAR_NAME "dlinear"
#endif
#ifndef DLINEAR_VERSION
#define DLINEAR_VERSION "file"
#endif

using std::string;
using std::ostream;
using std::endl;
using std::cerr;

namespace dlinear {

class ArgParser {
 private:
  argparse::ArgumentParser parser_;

  void addOptions();

 public:
  ArgParser();

  void parse(int argc, const char **argv);

  friend ostream &operator<<(ostream &os, const ArgParser &parser);

  [[nodiscard]] Config toConfig() const;

  template<typename T = std::string>
  [[nodiscard]] T get(const std::string &key) const { return parser_.get<T>(key); }

  friend ostream &operator<<(ostream &os, const dlinear::ArgParser &parser);
};

} // namespace dlinear



#endif //DLINEAR5_ARGPARSER_H
