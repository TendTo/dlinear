/**
 * @file ArgParser.h
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 * ArgParser class.
 *
 * Used to parse command line arguments.
 * Parse the command line arguments and convert them to Config.
 * The config object will then be used throughout the program.
 * The default values are defined in the configuration of the parser.
 */
#pragma once

#include <argparse/argparse.hpp>
#include <iostream>
#include <string>

#include "dlinear/util/Config.h"

namespace dlinear {

/**
 * Class used to parse command line arguments using the argparse library.
 * After parsing, a validation step is performed.
 */
class ArgParser {
 public:
  /** @constructor{argparser} */
  ArgParser();
  /**
   * Parse the command line arguments.
   * @param argc number of arguments
   * @param argv array of arguments as strings
   */
  void parse(int argc, const char **argv);

  /** @getter{version, program} */
  [[nodiscard]] static std::string version();
  /** @getter{hash status, repository} */
  [[nodiscard]] static std::string repositoryStatus();
  /** @getter{printable console prompt, program} */
  [[nodiscard]] std::string prompt() const;

  /**
   * Convert the parser to a @ref Config.
   *
   * The @ref Config object will be used throughout the program to pass the configuration
   * to all the components.
   * @return configuration object
   */
  [[nodiscard]] Config toConfig() const;

  /**
   * Get the value of a parameter from the internal parser.
   * @tparam T type of the parameter
   * @param key name of the parameter
   * @return value of the parameter
   * @throw std::invalid_argument if the key is not found
   */
  template <typename T = std::string>
  [[nodiscard]] T get(const std::string &key) const {
    return parser_.get<T>(key);
  }

  friend std::ostream &operator<<(std::ostream &os, const dlinear::ArgParser &parser);

 private:
  /** Add all the options, positional arguments and flags to the parser. */
  void addOptions();

  /**
   * Validate the options, ensuring the correctness of the parameters and the consistency of the options.
   * @throw std::invalid_argument if the options are inconsistent or incorrect.
   * @throw std::runtime_error if an error occurs during parsing.
   */
  void validateOptions();

  friend std::ostream &operator<<(std::ostream &os, const ArgParser &parser);

  argparse::ArgumentParser parser_;  ///< The parser object.
  size_t verbosity_;                 ///< Verbosity level of the program
  const std::string qsoptex_hash_;   ///< The hash of the QSoptEx library. Used in the prompt
  const std::string soplex_hash_;    ///< The hash of the Soplex library. Used in the prompt
};

}  // namespace dlinear
