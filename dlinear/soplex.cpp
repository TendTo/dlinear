#include "dlinear/libs/soplex.h"

#define PRECISION 9.999999999999996e-4

using namespace soplex;

int main(int argc, const char* argv[]) {
  if (argc < 2) {
    std::cout << "Usage: " << argv[0] << " <filename>" << std::endl;
    return 1;
  }

  SoPlex mysoplex;

  mysoplex.setRealParam(mysoplex.FEASTOL, PRECISION);
  mysoplex.setRealParam(mysoplex.OPTTOL, PRECISION);
  mysoplex.setBoolParam(mysoplex.RATREC, false);
  mysoplex.setIntParam(mysoplex.READMODE, mysoplex.READMODE_RATIONAL);
  mysoplex.setIntParam(mysoplex.SOLVEMODE, mysoplex.SOLVEMODE_RATIONAL);
  mysoplex.setIntParam(mysoplex.CHECKMODE, mysoplex.CHECKMODE_RATIONAL);
  mysoplex.setIntParam(mysoplex.SYNCMODE, mysoplex.SYNCMODE_AUTO);
  mysoplex.setIntParam(mysoplex.VERBOSITY, 3);
  // Default is maximize.
  mysoplex.setIntParam(mysoplex.OBJSENSE, mysoplex.OBJSENSE_MINIMIZE);
  // Enable precision boosting
  mysoplex.setBoolParam(mysoplex.ADAPT_TOLS_TO_MULTIPRECISION, true);
  mysoplex.setBoolParam(mysoplex.ITERATIVE_REFINEMENT, false);
  mysoplex.setIntParam(mysoplex.RATFAC_MINSTALLS, 0.0);

  mysoplex.printVersion();

  std::time_t start = std::time(nullptr);
  bool res = mysoplex.readFile(argv[1]);
  std::cout << "Read file: " << res << std::endl;
  std::cout << "Time: " << std::time(nullptr) - start << std::endl;

  // mysoplex.writeFile("dump_test.lp", NULL, NULL, NULL);

  return 0;
}
