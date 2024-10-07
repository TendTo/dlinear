/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Entry point of dLinear.
 * Run the dLinear program.
 *
 * Use the @verbatim-h @endverbatim flag to show the help tooltip.
 */
#include <iostream>

#include "dlinear/solver/SmtSolver.h"
#include "dlinear/solver/SmtSolverOutput.h"
#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Config.h"

int main(int argc, const char* argv[]) {
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
  if (!config.silent() && config.verify() && result.is_sat()) {
    if (solver.Verify(result.complete_model))
      std::cout << "Model correctly satisfies the input" << std::endl;
    else
      std::cerr << "WARNING: Model does not satisfy the input" << std::endl;
  }

  return result.exit_code();
}
