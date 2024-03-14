/**
 * @file main.cpp
 * @author dlinear
 * @date 28 Aug 2023
 * @copyright 2023 dlinear
 * @brief Main entry point for the benchmark program.
 *
 * The main function is used to start the benchmark program.
 */
#include <csignal>

#include "benchmark/BenchmarkProgram.h"

using dlinear::benchmark::BenchmarkProgram;

namespace {
void HandleSigInt(const int) {
  // Properly exit so that we can see stat information produced by destructors
  // even if a user press C-c.
  std::exit(1);
}
}  // namespace

int main(int argc, const char *argv[]) {
  std::signal(SIGINT, HandleSigInt);
  BenchmarkProgram main_program{argc, argv};
  return main_program.Run();
}
