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
#include "dlinear/MainProgram.h"

using dlinear::MainProgram;

namespace {
void HandleSigInt(const int) {
  // Properly exit so that we can see stat information produced by destructors
  // even if a user press C-c.
  std::exit(1);
}
}  // namespace

int main(int argc, const char *argv[]) {
  std::signal(SIGINT, HandleSigInt);
  MainProgram main_program{argc, argv};
  throw std::runtime_error("test");
  return main_program.Run();
}
