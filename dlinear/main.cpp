/**
 * @file main.h
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 * Entry point of dLinear.
 * Run the dLinear program.
 *
 * Use the @verbatim-h@verbatim flag to show the help tooltip.
 */
#include <csignal>

#include "dlinear/solver/Solver.h"
#include "dlinear/solver/SolverOutput.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Infinity.h"

namespace {
void HandleSigInt(const int) {
  // Properly exit so that we can see stat information produced by destructors
  // even if a user press C-c.
  std::exit(EXIT_FAILURE);
}
}  // namespace

int main(int argc, const char* argv[]) {
  // Handle C-c.
  std::signal(SIGINT, HandleSigInt);

  // Initialize the command line parser.
  dlinear::ArgParser parser{};
  // Parse the command line arguments.
  parser.parse(argc, argv);
  // Get the configuration from the command line arguments.
  dlinear::Config config = parser.toConfig();

  // Setup the infinity values.
  dlinear::Solver solver{config};

  if (!config.silent()) std::cout << solver.CheckSat() << std::endl;

  return 0;
}
