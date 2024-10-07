/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Driver form the parsing and execution of vnnlib files.
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

#include "dlinear/parser/Driver.h"
#include "dlinear/parser/vnnlib/FunctionDefinition.h"
#include "dlinear/parser/vnnlib/Term.h"
#include "dlinear/parser/vnnlib/scanner.h"
#include "dlinear/solver/Context.h"
#include "dlinear/util/ScopedUnorderedMap.hpp"

namespace dlinear::vnnlib {

/**
 * The VnnlibDriver class brings together all components. It creates an
 * instance of the Parser and Scanner classes and connects them. Then
 * the input stream is fed into the scanner object and the parser gets
 * it's token sequence. Furthermore the driver object is available in
 * the grammar rules as a parameter. Therefore the driver class
 * contains a reference to the structure into which the parsed data is
 * saved.
 */
class VnnlibDriver : public Driver {
 public:
  /// construct a new parser driver context
  explicit VnnlibDriver(Context &context);  // NOLINT(runtime/references): Reference context filled during parsing.

  /**
   * Error handling with associated line number. This can be modified to
   * output the error e.g. to a dialog box.
   */
  static void error(const location &l, const std::string &m);

  bool ParseStreamCore(std::istream &in) override;

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

  /**
   * Pointer to the current scanner instance, this is used to connect the
   * parser to the scanner. It is used in the yylex macro.
   */
  VnnlibScanner *scanner() { return scanner_; }

 private:
  VnnlibScanner *scanner_{nullptr};  ///< The scanner producing the tokens for the parser.

  ScopedUnorderedMap<std::string, Expression> scope_constants_;          ///< Scoped map from a name to a constant
  ScopedUnorderedMap<std::string, Variable> scope_variables_;            ///< Scoped map from a name to a Variable
  ScopedUnorderedMap<std::string, FunctionDefinition> scope_functions_;  ///< Scoped map from a name to a Function

  int64_t nextUniqueId_{};  ///< Sequential value concatenated to names to make them unique.
};

}  // namespace dlinear::vnnlib
