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

#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/libs/soplex.h"
#include "dlinear/smt2/run.h"
#include "dlinear/solver/Context.h"
#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Infinity.h"

namespace {
void HandleSigInt(const int) {
  // Properly exit so that we can see stat information produced by destructors
  // even if a user press C-c.
  std::exit(1);
}
}  // namespace

int main(int argc, const char *argv[]) {
  // Handle C-c.
  std::signal(SIGINT, HandleSigInt);

  // Initialize the command line parser.
  dlinear::ArgParser parser{QSopt_ex_repository_status(), soplex::getGitHash()};
  // Parse the command line arguments.
  parser.parse(argc, argv);
  // Get the configuration from the command line arguments.
  dlinear::Config config_ = parser.toConfig();

  // Initialize the infinity values for the chosen LP solver.
  dlinear::Infinity::InftyStart(config_);
  // Run the smt2 parser on the input file.
  dlinear::RunSmt2(config_);
  // Clean up the infinity values.
  dlinear::Infinity::InftyFinish();
  return 0;
}
