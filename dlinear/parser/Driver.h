/**
 * @file Driver.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Driver class
 *
 * The Driver is the base class for all the parsers.
 * It contains the common logic to allow the parsed data to be saved in the context.
 * It coordinates the communication between the parser (bison) and the scanner (flex).
 */
#pragma once

#include <string>

#include "dlinear/solver/Context.h"
#include "dlinear/solver/Logic.h"

namespace dlinear {

/**
 * The Driver is the base class for all the parsers.
 *
 * It contains the common logic to allow the parsed data to be saved in the context.
 * It coordinates the communication between the parser (bison) and the scanner (flex).
 */
class Driver {
 public:
  /// construct a new parser driver context
  explicit Driver(Context &context, const std::string &class_name = "Driver");
  virtual ~Driver() = default;

  /**
   * Invoke the scanner and parser for a stream.
   * @param in input stream
   * @param sname stream name for error messages
   * @return true if successfully parsed
   * @return false if an error occurred
   */
  bool ParseStream(std::istream &in, const std::string &sname = "stream input");

  /**
   * Invoke the scanner and parser on an input string.
   * @param input input string
   * @param sname stream name for error messages
   * @return true if successfully parsed
   * @return false if an error occurred
   */
  bool ParseString(const std::string &input, const std::string &sname = "string stream");

  /**
   * Invoke the scanner and parser on a file.
   *
   * Use parse_stream with a std::ifstream if detection of file reading errors is required.
   * @param filename input file name
   * @return true if successfully parsed
   * @return false if an error occurred
   */
  bool ParseFile(const std::string &filename);

  /** General error handling. */
  static void Error(const std::string &m);

  void Push(int n) { context_.Push(n); }
  void Pop(int n) { context_.Pop(n); }

  void Assert(const Formula &f) { context_.Assert(f); }

  /** Call context_.CheckSat() and print proper output messages to the standard output. */
  void CheckSat();

  /** Return a model computed by the solver in response to an invocation of the check-sat. */
  void GetModel();

  /**
   * @smtcommand{get-assertions, Print all the assertions currently in the context.
   * If the mode is set to silent\, it does not print anything.}
   */
  void GetAssertions() const;

  /**
   * @smtcommand{get-option, Print the value of and option or an empty string if the option is not set
   * @param key key of the option}
   */
  void GetOption(const std::string &key) const;

  /**
   * @smtcommand{get-info, Print information about the solver or the current context.
   * @param key key of the information to print}
   */
  void GetInfo(const std::string &key) const;

  void SetInfo(const std::string &key, const std::string &value) { context_.SetInfo(key, value); }
  void SetOption(const std::string &key, const std::string &value) { context_.SetOption(key, value); }
  void SetLogic(const Logic logic) { context_.SetLogic(logic); }

  /**
   * Maximize the objective function @p f. The objective function is
   * added to the context as a constraint.
   * @param f expression to maximize
   */
  void Maximize(const Expression &f);

  /**
   * Minimize the objective function @p f. The objective function is
   * added to the context as a constraint.
   * @param f expression to minimize
   */
  void Minimize(const Expression &f);

  void Exit() { context_.Exit(); }

  [[nodiscard]] bool trace_scanning() const { return debug_scanning_; }
  [[nodiscard]] bool trace_parsing() const { return debug_parsing_; }
  [[nodiscard]] const Context &context() const { return context_; }
  [[nodiscard]] const std::string &stream_name() const { return stream_name_; }
  std::string &m_stream_name() { return stream_name_; }

  /**
   * Statistics for the driver.
   * @return statistics for the driver
   */
  [[nodiscard]] const Stats &stats() const { return stats_; }

 protected:
  virtual bool ParseStreamCore(std::istream &in) = 0;

  std::string stream_name_;  ///< The name of the stream being parsed.

  Context &context_;  ///< The context filled during parsing of the expressions.

  bool debug_scanning_{false};  ///< Enable debug output in the flex scanner.

  bool debug_parsing_{false};  ///< Enable debug output in the bison parser.

  Stats stats_;   ///< Statistics for the driver.
  Timer *timer_;  ///< Pointer to the timer for the driver. Used to pause the timer when checking sat.
};

}  // namespace dlinear
