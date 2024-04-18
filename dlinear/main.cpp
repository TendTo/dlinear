/**
 * @file main.cpp
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 * Entry point of dLinear.
 * Run the dLinear program.
 *
 * Use the @verbatim-h @endverbatim flag to show the help tooltip.
 */
#include <csignal>

#include "dlinear/solver/SmtSolver.h"
#include "dlinear/solver/SmtSolverOutput.h"
#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Config.h"

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
  dlinear::SmtSolver solver{config};

  // Run the solver
  dlinear::SmtSolverOutput result = solver.Parse();
  if (result.result == dlinear::SmtResult::UNSOLVED && config.enforce_check_sat()) result = solver.CheckSat();
  if (!config.silent() && !result.matches_expectation(solver.GetExpected())) {
    std::cerr << "WARNING: Expected " << solver.GetExpected() << " but got " << result.result << std::endl;
  }

  return result.exit_code();
}
