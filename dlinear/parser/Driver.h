/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Driver class.
 */
#pragma once

#include <iosfwd>
#include <string>

#include "dlinear/solver/Context.h"
#include "dlinear/solver/Logic.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"

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
  virtual bool ParseFile(const std::string &filename);

  /** General error handling. */
  static void Error(const std::string &m);

  /**
   * Push the current context to the stack.
   *
   * The current state of the context can be restored by calling Pop.
   * @param n number of stacks to push
   */
  void Push(int n) { context_.Push(n); }
  /**
   * Restore a previously pushed context from the stack.
   *
   * The current state of the context can be stored by calling Push.
   * @param n number of stacks to pop
   */
  void Pop(int n) { context_.Pop(n); }

  void Assert(const Formula &f) { context_.Assert(f); }

  /** Call context_.CheckSat() and print proper output messages to the standard output. */
  void CheckSat();

  /** Return a model computed by the solver in response to an invocation of the check-sat. */
  void GetModel();

  /**
   * @smtcommand{get-assertions, Print all the assertions currently in the context.
     If the mode is set to silent\, it does not print anything.}
   */
  void GetAssertions() const;

  /**
   * @smtcommand{get-option, Print the value of and option or an empty string if the option is not set.
     @param key key of the option}
   */
  void GetOption(const std::string &key) const;

  /**
   * @smtcommand{get-info, Print information about the solver or the current context.
     @param key key of the information to print}
   */
  void GetInfo(const std::string &key) const;
  /**
   * @smtcommand{set-info, Set the @p value of the information identified by @p key.
     @param key key of the information to set
     @param value value of the information}
   */
  void SetInfo(const std::string &key, const std::string &value) { context_.SetInfo(key, value); }
  /**
   * @smtcommand{set-option, Set the @p value of the option identified by @p key.
     @param key key of the option to set
     @param value value of the option}
   */
  void SetOption(const std::string &key, const std::string &value) { context_.SetOption(key, value); }
  /**
   * @smtcommand{set-logic, Set the @p logic used through the input.
     @param logic smt-lib logic}
   */
  void SetLogic(const Logic logic) { context_.SetLogic(logic); }

  /**
   * Maximize the objective function @p f. The objective function is
   * added to the context as a constraint.
   * @param f expression to maximize}
   */
  void Maximize(const Expression &f);

  /**
   * Minimize the objective function @p f. The objective function is
   * added to the context as a constraint.
   * @param f expression to minimize
   */
  void Minimize(const Expression &f);

  /** @smtcommand{exit, Terminate the parsing} */
  void Exit() { context_.Exit(); }

  /** @checker{enabled, scanner debugger} */
  [[nodiscard]] bool trace_scanning() const { return debug_scanning_; }
  /** @checker{enabled, trace debugger} */
  [[nodiscard]] bool trace_parsing() const { return debug_parsing_; }
  /** @getter{enabled, Driver} */
  [[nodiscard]] const Context &context() const { return context_; }
  /** @getter{stream name, input being parsed} */
  [[nodiscard]] const std::string &stream_name() const { return stream_name_; }
  /** @getsetter{stream name, input being parsed} */
  std::string &m_stream_name() { return stream_name_; }

  /**
   * Statistics for the driver.
   * @return statistics for the driver
   */
  [[nodiscard]] const Stats &stats() const { return stats_; }

 protected:
  /**
   * Parse the stream.
   * @param in input stream
   * @return true if successfully parsed
   * @return false if an error occurred
   */
  virtual bool ParseStreamCore(std::istream &in) = 0;

  std::string stream_name_;  ///< The name of the stream being parsed.

  Context &context_;  ///< The context filled during parsing of the expressions.

  bool debug_scanning_{false};  ///< Enable debug output in the flex scanner.

  bool debug_parsing_{false};  ///< Enable debug output in the bison parser.

  Stats stats_;   ///< Statistics for the driver.
  Timer *timer_;  ///< Pointer to the timer for the driver. Used to pause the timer when checking sat.
};

}  // namespace dlinear
