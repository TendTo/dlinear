/**
 * @file Sense.h
 * @author dlinear
 * @date 16 Sep 2023
 * @copyright 2023 dlinear
 *
 * @brief Sense of a constraint row.
 *
 * The sense indicates the type or relation a contraint row has with
 * respect to its right-hand side.
 * The supported values are 'L', 'E', 'G', or 'N'.
 * They represent, respectively, less than, equal to, greater than, or
 * no constraint, usually applied to the objective function.
 */
#include "dlinear/mps/Driver.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/logging.h"
#include "dlinear/util/Infinity.h"
#include "dlinear/util/Config.h"

#define TRACE false

int main(int, char const *[]) {
  DLINEAR_LOG_INIT_VERBOSITY(5);

  dlinear::Infinity::InftyStart(dlinear::Config::LPSolver::QSOPTEX);
  dlinear::Expression::InitConstants();

  dlinear::mps::MpsDriver driver;
  driver.set_debug_parsing(TRACE);
  driver.set_debug_scanning(TRACE);

  return driver.parse_file("/home/tend/Programming/tesi/dlinear5/tests/test3.mps");
}
