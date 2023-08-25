/**
 * @file run.cpp
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 */
#include "run.h"

namespace dlinear {

using std::string;

void RunSmt2(const Config &config) {
  DLINEAR_TRACE_FMT("RunSmt2({})", config);

  Smt2Driver smt2_driver{Context{config}};
  // Set up --debug-scanning option.
  smt2_driver.set_trace_scanning(config.debug_scanning());
  DLINEAR_DEBUG_FMT("RunSmt2() --debug-scanning = {}", smt2_driver.trace_scanning());
  // Set up --debug-parsing option.
  smt2_driver.set_trace_parsing(config.debug_parsing());
  DLINEAR_DEBUG_FMT("RunSmt2() --debug-parsing = {}", smt2_driver.trace_parsing());
  smt2_driver.parse_file(config.filename());

  DLINEAR_TRACE("RunSmt2() -- Finished parsing file.");
}

}  // namespace dlinear
