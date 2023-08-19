/**
 * @file test.cpp
 * @author dlinear
 * @date 10 Aug 2023
 * @copyright 2023 dlinear
 */
#include "dlinear/util/logging.h"
#include "dlinear/util/ArgParser.h"

#include <unistd.h>

int main([[maybe_unused]] int argc, [[maybe_unused]] const char **argv) {
  DLINEAR_LOG_INIT_VERBOSITY(5);

  dlinear::ArgParser parser;
  parser.parse(argc, argv);
  dlinear::Config config = parser.toConfig();
  std::cout << config << std::endl;
  return 0;
}
