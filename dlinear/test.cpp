#include "dlinear/solver/Context.h"
#include "dlinear/solver/Solver.h"

#define PRECISION 9.999999999999996e-4

using namespace dlinear;

int main(int argc, const char* argv[]) {
  if (argc < 2) {
    std::cout << "Usage: " << argv[0] << " <filename>" << std::endl;
    return 1;
  }

  Config c{std::string(argv[1])};
  c.mutable_skip_check_sat() = true;
  Solver s{c};
  s.CheckSat();
}
