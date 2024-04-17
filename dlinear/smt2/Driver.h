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
#pragma once

#include <istream>
#include <string>
#include <utility>
#include <variant>
#include <vector>

#include "dlinear/smt2/FunctionDefinition.h"
#include "dlinear/smt2/Term.h"
#include "dlinear/smt2/scanner.h"
#include "dlinear/solver/Context.h"
#include "dlinear/util/ScopedUnorderedMap.hpp"
#include "dlinear/util/Stats.h"

namespace dlinear::smt2 {

/**
 * The Smt2Driver class brings together all components. It creates an
 * instance of the Parser and Scanner classes and connects them. Then
 * the input stream is fed into the scanner object and the parser gets
 * it's token sequence. Furthermore the driver object is available in
 * the grammar rules as a parameter. Therefore the driver class
 * contains a reference to the structure into which the parsed data is
 * saved.
 */
class Smt2Driver {
 public:
  /// construct a new parser driver context
  explicit Smt2Driver(Context &context);  // NOLINT(runtime/references): Reference context filled during parsing.

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

  // To demonstrate pure handling of parse errors, instead of
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

  /** Call context_.CheckSat() and print proper output messages to cout. */
  void CheckSat();

  /**
   * Eliminate Boolean variables @f$ [b_1, …, b_n] \in @f$ @p vars from @p f.
   *
   * This is done by constructing @f$ f[b \to \text{true}] \land f[b \to \text{false}] @f$.
   * Used in handling `forall` terms.
   * @param vars set of variables to eliminate
   * @param f formula to eliminate the variables from
   * @return formula with the variables eliminated
   */
  static Formula EliminateBooleanVariables(const Variables &vars, const Formula &f);

  /**
   * Called by the `define-fun` command in the SMT-2 file.
   *
   * It defines a function with name @p name, parameters @p parameters, return type @p return_type, and body @p body.
   * @param name name of the function
   * @param parameters parameters the function takes
   * @param return_type return type of the function
   * @param body body of the function
   */
  void DefineFun(const std::string &name, const std::vector<Variable> &parameters, Sort return_type, const Term &body);

  /**
   * Register a variable with name @p name and sort @p s in the scope. Note
   * that it does not declare the variable in the context.
   */
  Variable RegisterVariable(const std::string &name, Sort sort);

  /** Declare a variable with name @p name and sort @p sort. */
  Variable DeclareVariable(const std::string &name, Sort sort);

  /** Declare a variable with name @p name and sort @p sort which is bounded by an interval `[lb, ub]` */
  void DeclareVariable(const std::string &name, Sort sort, const Term &lb, const Term &ub);

  /** Declare a new variable with label @p name that is globally unique and cannot occur in an SMT-LIBv2 file. */
  Variable DeclareLocalVariable(const std::string &name, Sort sort);

  /** Define a constant within the current scope. */
  void DefineLocalConstant(const std::string &name, const Expression &value);

  /**
   * Get the value of all the terms in @p term_list.
   *
   * Maps each term @f$ t_i \in @f$ @p term_list to its value @f$ v_i @f$ in the current model.
   * @param term_list list of terms to get the value of
   */
  void GetValue(const std::vector<Term> &term_list) const;

  /** Return a model computed by the solver in response to an invocation of the check-sat. */
  void GetModel();

  /**
   * Get the value of an option @p key.
   * @param key key of the option
   */
  void GetOption(const std::string &key) const;

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

  /**
   * Lookup a variable or constant expression associated with a name @p name.
   * @param name name of the variable or constant expression
   * @return the variable or constant expression with name @p name
   * @throw std::out_or_range std:: if no variable or constant expression is associated with @p name
   */
  std::variant<const Expression *, const Variable *> LookupDefinedName(const std::string &name) const;
  /**
   * Lookup a constant expression associated with a name @p name.
   * @param name name of the constant expression
   * @return the constant expression with name @p name
   * @throw std::out_or_range std:: if no constant expression is associated with @p name
   */
  const Expression &LookupConstant(const std::string &name) const;
  /**
   * Lookup a variable associated with a name @p name.
   * @param name name of the variable
   * @return the variable with name @p name
   * @throw std::out_or_range if no variable is associated with @p name
   */
  const Variable &LookupVariable(const std::string &name) const;
  /**
   * Lookup a function with name @p name and run it with @p arguments, producing a new term.
   * @param name name of the function
   * @param arguments arguments to pass to the function
   * @return output of the function @p name with @p arguments
   * @throw std::out_or_range if no function is associated with @p name
   * @throw std::runtime_error if the function is incompatible with the @p arguments
   */
  Term LookupFunction(const std::string &name, const std::vector<Term> &arguments) const;

  void PushScope() { scope_variables_.push(); }

  void PopScope() { scope_variables_.pop(); }

  std::string MakeUniqueName(const std::string &name);

  bool trace_scanning() const { return debug_scanning_; }
  void set_trace_scanning(bool b) { debug_scanning_ = b; }

  bool trace_parsing() const { return debug_parsing_; }
  void set_trace_parsing(bool b) { debug_parsing_ = b; }

  Context &m_context() { return context_; }
  const Context &context() const { return context_; }

  std::string &m_streamname() { return streamname_; }

  /**
   * Pointer to the current scanner instance, this is used to connect the
   * parser to the scanner. It is used in the yylex macro.
   */
  Smt2Scanner *scanner() { return scanner_; }

  /**
   * Statistics for the driver.
   * @return statistics for the driver
   */
  const Stats &stats() const { return stats_; }

 private:
  Smt2Scanner *scanner_{nullptr};  ///< The scanner producing the tokens for the parser.

  ScopedUnorderedMap<std::string, Expression> scope_constants_;          ///< Scoped map from a name to a constant
  ScopedUnorderedMap<std::string, Variable> scope_variables_;            ///< Scoped map from a name to a Variable
  ScopedUnorderedMap<std::string, FunctionDefinition> scope_functions_;  ///< Scoped map from a name to a Function

  int64_t nextUniqueId_{};  ///< Sequential value concatenated to names to make them unique.

  std::string streamname_;  ///< The name of the stream being parsed.

  Context &context_;  ///< The context filled during parsing of the expressions.

  bool debug_scanning_{false};  ///< Enable debug output in the flex scanner.

  bool debug_parsing_{false};  ///< Enable debug output in the bison parser.

  Stats stats_;  ///< Statistics for the driver.
};

}  // namespace dlinear::smt2
