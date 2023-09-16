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
// Argparse is a header-only library for parsing command line arguments.
#include <argparse/argparse.hpp>

#include "dlinear/util/Config.h"

namespace dlinear {

class ArgParser {
 private:
  argparse::ArgumentParser parser_;
  std::string qsoptex_hash_;
  std::string soplex_hash_;

  void addOptions();

  void validateOptions();

 public:
  ArgParser();
  explicit ArgParser(std::string qsopt_exHash, std::string soplexHash = "");

  void parse(int argc, const char **argv);

  [[nodiscard]] std::string version() const;

  [[nodiscard]] std::string repositoryStatus() const;

  [[nodiscard]] std::string prompt() const;

  friend std::ostream &operator<<(std::ostream &os, const ArgParser &parser);

  [[nodiscard]] Config toConfig() const;

  template <typename T = std::string>
  [[nodiscard]] T get(const std::string &key) const {
    return parser_.get<T>(key);
  }

  friend std::ostream &operator<<(std::ostream &os, const dlinear::ArgParser &parser);
};

}  // namespace dlinear
