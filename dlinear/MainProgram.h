/**
 * @file MainProgram.h
 * @author tend
 * @date 12 Aug 2023
 * @copyright 2023 tend
 * @brief Brief description
 *
 * Long Description
 */

#ifndef DLINEAR5_DLINEAR_MAINPROGRAM_H_
#define DLINEAR5_DLINEAR_MAINPROGRAM_H_

#include "dlinear/util/Config.h"
#include "dlinear/util/ArgParser.h"
#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/libs/soplex.h"

using std::cerr;
using std::cout;
using std::endl;
using std::numeric_limits;
using std::string;
using std::vector;

namespace dlinear {

/**
 * The main program is responsible for parsing command line options,
 * processing the input file, and outputting the result.
 */
class MainProgram {
 public:
  /** Constructor.
   * @param argc Number of arguments.
   * @param argv Arguments.
   */
  MainProgram(int argc, const char *argv[]);

  /** Executes the main program.
   * @return 0 if success, 1 if failure.
   */
  int Run();

 private:
  void PrintUsage();
  void AddOptions();
  void Init();
  void DeInit();
  bool ValidateOptions();

  void ExtractOptions();

  bool is_options_all_valid_{false};
  ArgParser parser_;
  Config config_;
};

} // dlinear

#endif //DLINEAR5_DLINEAR_MAINPROGRAM_H_