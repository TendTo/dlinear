/**
 * @file TestSmt2.cpp
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 */
#include "dlinear/solver/Solver.h"
#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Config.h"

using dlinear::ArgParser;
using dlinear::Config;
using dlinear::Solver;

int main(int argc, const char *argv[]) {
  ArgParser argParser;
  argParser.parse(argc, argv);
  Config config = argParser.toConfig();

  Solver solver{config};
  std::cout << solver.CheckSat() << std::endl;

  return 0;
}