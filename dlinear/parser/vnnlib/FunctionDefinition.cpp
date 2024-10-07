/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "FunctionDefinition.h"

#include <utility>

#include "dlinear/util/exception.h"

namespace dlinear::vnnlib {

FunctionDefinition::FunctionDefinition(std::vector<Variable> parameters, Sort return_type, Term body)
    : parameters_{std::move(parameters)}, return_type_{return_type}, body_{std::move(body)} {
  body_.Check(return_type_);
}

Term FunctionDefinition::operator()(const std::vector<Term>& arguments) const {
  if (parameters_.size() != arguments.size()) {
    DLINEAR_RUNTIME_ERROR_FMT("This function definition expects #{} arguments ({}). Provided #{} arguments.",
                              parameters_.size(), parameters_, arguments.size());
  }
  Term t = body_;

  for (std::size_t i = 0; i < parameters_.size(); ++i) {
    const Variable& param_i{parameters_[i]};
    const Term& arg_i{arguments[i]};
    arg_i.Check(param_i.get_type());
    t = t.Substitute(param_i, arg_i);
  }

  return t;
}

}  // namespace dlinear::vnnlib
