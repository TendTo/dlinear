/**
 * @file Driver.h
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 * @brief Driver form the parsing and execution of smt2 files.
 *
 * The driver puts in communication the parser and the scanner.
 * In the end, it produces a context that can be used to solve the
 * problem.
 */
#ifndef DLINEAR5_DLINEAR_SMT2_DRIVER_H_
#define DLINEAR5_DLINEAR_SMT2_DRIVER_H_

#include <istream>
#include <string>
#include <utility>

#include "dlinear/mps/scanner.h"

namespace dlinear {

/**
 * The MpsDriver class brings together all components. It creates an
 * instance of the Parser and Scanner classes and connects them. Then
 * the input stream is fed into the scanner object and the parser gets
 * it's token sequence. Furthermore the driver object is available in
 * the grammar rules as a parameter. Therefore the driver class
 * contains a reference to the structure into which the parsed data is
 * saved.
 */
class MpsDriver {
 public:
  /// construct a new parser driver context
  MpsDriver() = default;

  /**
   * Invoke the scanner and parser for a stream.
   * @param in	input stream
   * @param sname	stream name for error messages
   * @return		true if successfully parsed
   */
  bool parse_stream(std::istream &in, const std::string &sname = "stream input");

  /**
   * Invoke the scanner and parser on an input string.
   * @param input	input string
   * @param sname	stream name for error messages
   * @return		true if successfully parsed
   */
  bool parse_string(const std::string &input, const std::string &sname = "string stream");

  /**
   * Invoke the scanner and parser on a file. Use parse_stream with a
   * std::ifstream if detection of file reading errors is required.
   * @param filename	input file name
   * @return		true if successfully parsed
   */
  bool parse_file(const std::string &filename);

  // simply dumping them on the standard error output, we will pass
  // them to the driver using the following two member functions.

  /**
   * Error handling with associated line number. This can be modified to
   * output the error e.g. to a dialog box.
   */
  static void error(const location &l, const std::string &m);

  /**
   * General error handling. This can be modified to output the error
   * e.g. to a dialog box.
   */
  static void error(const std::string &m);

  void print(int number) const;
  void print(const std::string str) const;

  void AddRow(char sense, const std::string &name);
  void AddColumn(const std::string &row, const std::string &column, double value);
  void AddRhs(const std::string &row, const std::string &rhs, double value);
  void AddRange(const std::string &row, const std::string &rhs, double value);
  void AddBound(const std::string &row, const std::string &bound, double value, const std::string &type);

  std::string &mutable_streamname() { return streamname_; }

  std::string streamname_;
  bool trace_scanning_{false};
  bool trace_parsing_{false};
  MpsScanner *scanner_{nullptr};
};

}  // namespace dlinear

#endif  // DLINEAR5_DLINEAR_SMT2_DRIVER_H_
