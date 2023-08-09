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
#include "dlinear/libs/gmp.h"

using dlinear::ArgParser;
using dlinear::Config;
using dlinear::gmp::add;;

int main(int argc, const char *argv[]) {
  mpz_class a{1}, b{2};
  mpz_class sum = add(a, b);
  std::cout << sum << std::endl;
  ArgParser parser{};
  parser.parse(argc, argv);
  Config c = parser.toConfig();
  std::cout << c << std::endl;
}
