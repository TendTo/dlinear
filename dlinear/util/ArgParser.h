/**
 * @file ArgParser.h
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 * ArgParser class.
 * Used to parse command line arguments.
 *
 * Parse the command line arguments and convert them to Config.
 * The config object will then be used throughout the program.
 * The default values are defined in the configuration of the parser.
 */
#pragma once

#include <iostream>
#include <string>

// Argparser library
#include <argparse/argparse.hpp>

#include "dlinear/util/Config.h"

namespace dlinear {

/**
 * Class used to parse command line arguments using the argparse library.
 * After parsing, a validation step is performed.
 */
class ArgParser {
 private:
  argparse::ArgumentParser parser_;  ///< The parser object.
  std::string qsoptex_hash_;         ///< The hash of the QSoptEx library. Used in the prompt
  std::string soplex_hash_;          ///< The hash of the Soplex library. Used in the prompt

  /**
   * Add all the options, positional arguments and flags to the parser.
   */
  void addOptions();

  /**
   * Validate the options, ensuring the correctness of the parameters and the consistency of the options.
   * @throw std::invalid_argument if the options are inconsistent or incorrect.
   * @throw std::runtime_error if an error occurs during parsing.
   */
  void validateOptions();

 public:
  ArgParser();
  explicit ArgParser(std::string qsopt_exHash, std::string soplexHash = "");

  /**
   * Parse the command line arguments.
   * @param argc number of arguments
   * @param argv array of arguments as strings
   */
  void parse(int argc, const char **argv);

  /**
   * Version of the program.
   * @return version of the program
   */
  [[nodiscard]] static std::string version();
  /**
   * Status of the repository.
   * @return status of the repository
   */
  [[nodiscard]] static std::string repositoryStatus();
  /**
   * Complete prompt to print on the console.
   * @return complete prompt
   */
  [[nodiscard]] std::string prompt() const;

  friend std::ostream &operator<<(std::ostream &os, const ArgParser &parser);
  /**
   * Convert the parser to a @ref Config.
   *
   * The @ref Config object will be used throughout the program to pass the configuration
   * to all the components.
   * @return configuration object
   */
  [[nodiscard]] Config toConfig() const;

  template <typename T = std::string>
  [[nodiscard]] T get(const std::string &key) const {
    return parser_.get<T>(key);
  }

  friend std::ostream &operator<<(std::ostream &os, const dlinear::ArgParser &parser);
};

}  // namespace dlinear
