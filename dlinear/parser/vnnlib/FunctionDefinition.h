/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Function definition class
 *
 * In the VNNLIB language, a function definition is a way to define a function in terms of its parameters and body.
 * A function defined in this way can be called with the operator() method by providing the required arguments.
 */
#pragma once

#include <concepts>
#include <cstddef>
#include <vector>

#include "dlinear/parser/vnnlib/Sort.h"
#include "dlinear/parser/vnnlib/Term.h"
#include "dlinear/symbolic/literal.h"

namespace dlinear::vnnlib {

/**
 * A new function defined by the user in the VNNLIB language using the `define-fun` command.
 *
 * In the VNNLIB language, a function definition is a way to define a function in terms of its parameters and body.
 * A function defined in this way can be called with the operator() method by providing the required arguments.
 * @code
 * // Example usage:
 * const Variable lhs{"lhs"}, rhs{"rhs"};
 * const FunctionDefinition fun_sum{{lhs_, rhs_}, Sort::Real, Term{lhs_ + rhs_}};
 *
 * Term res = fun_sum(Term{5}, Term{6});
 *
 * std::cout << res << std::endl;
 * // Output:
 * // 11
 * @endcode
 */
class FunctionDefinition {
 public:
  /**
   * Construct a new function definition.
   *
   * The function will accept parameters of the given types and return a value of the given type when called.
   * @param parameters parameters of the function
   * @param return_type return type of the function
   * @param body body of the function
   */
  FunctionDefinition(std::vector<Variable> parameters, Sort return_type, Term body);

  /**
   * Call the function with the given arguments.
   * @param arguments arguments to the function
   * @return the result of the function
   */
  Term operator()(const std::vector<Term>& arguments) const;
  /**
   * Call the function with the given arguments.
   * @param arguments arguments to the function
   * @return the result of the function
   */
  Term operator()(std::same_as<Term> auto... arguments) const {
    if (parameters_.size() != sizeof...(arguments)) {
      throw std::runtime_error("This function definition expects #" + std::to_string(parameters_.size()) +
                               " arguments ({}). Provided #" + std::to_string(sizeof...(arguments)) + " arguments.");
    }
    Term t = body_;

    std::size_t i = 0;
    for (const Term& arg_i : {arguments...}) {
      const Variable& param_i{parameters_[i]};
      arg_i.Check(param_i.get_type());
      t = t.Substitute(param_i, arg_i);
      ++i;
    }

    return t;
  }

 private:
  std::vector<Variable> parameters_;  ///< Parameters of the function
  Sort return_type_;                  ///< Return type of the function
  Term body_;                         ///< Body of the function
};

}  // namespace dlinear::vnnlib
