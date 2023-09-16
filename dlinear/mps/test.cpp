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
