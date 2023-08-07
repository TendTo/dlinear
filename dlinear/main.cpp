/**
 * @file main.h
 * @author tend
 * @date 07 Aug 2023
 * @copyright 2023 tend
 * @brief Main file.
 * Run the dLinear program.
 *
 * Use the @verbatim-h@verbatim flag to show the help tooltip.
 */
#include <iostream>
#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Config.h"

using dlinear::ArgParser;
using dlinear::Config;

int main(int argc, const char *argv[]) {
  ArgParser parser{};
  parser.parse(argc, argv);
  Config c = parser.toConfig();
  std::cout << c << std::endl;
}
