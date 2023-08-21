#include "run.h"

namespace dlinear {

using std::string;

void RunSmt2(const string &filename, const Config &config, const bool debug_scanning, const bool debug_parsing) {
  Smt2Driver smt2_driver{Context{config}};
  // Set up --debug-scanning option.
  smt2_driver.set_trace_scanning(debug_scanning);
  DLINEAR_DEBUG_FMT("RunSmt2() --debug-scanning = {}", smt2_driver.trace_scanning());
  // Set up --debug-parsing option.
  smt2_driver.set_trace_parsing(debug_parsing);
  DLINEAR_DEBUG_FMT("RunSmt2() --debug-parsing = {}", smt2_driver.trace_parsing());
  smt2_driver.parse_file(filename);
}

}  // namespace dlinear
