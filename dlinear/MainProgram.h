/**
 * @file MainProgram.h
 * @author dlinear
 * @date 12 Aug 2023
 * @copyright 2023 dlinear
 * @brief Entrypoint for the dlinear program.
 *
 * Runs the dlinear program.
 * The command line options are used to produce the correct Configuration for the solver.
 */

#ifndef DLINEAR5_DLINEAR_MAINPROGRAM_H_
#define DLINEAR5_DLINEAR_MAINPROGRAM_H_

#include "dlinear/util/Config.h"
#include "dlinear/util/ArgParser.h"
#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/libs/soplex.h"
#include "dlinear/solver/Context.h"
#include "dlinear/smt2/run.h"

namespace dlinear {

/**
 * The main program is responsible for parsing command line options,
 * processing the input file, and outputting the result.
 */
class MainProgram {
 public:
  /**
   * Constructor.
   * @param argc Number of arguments.
   * @param argv Arguments.
   */
  MainProgram(int argc, const char *argv[]);

  /**
   * Executes the main program.
   * @return 0 if success, 1 if failure.
   */
  int Run();

 private:
  /** Initialize all the constants the libraries expect. */
  void Init();
  /** Free all the constants used by the libraries. */
  void DeInit();

  Config config_; ///< Configuration for the program. All default can be overridden by command line options.
};

} // namespace dlinear

#endif //DLINEAR5_DLINEAR_MAINPROGRAM_H_
