/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */

#include "dlinear/parser/smt2/Driver.h"

#include <iostream>
#include <sstream>

#include "dlinear/symbolic/ExpressionEvaluator.h"
#include "dlinear/symbolic/PrefixPrinter.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear::smt2 {

Smt2Driver::Smt2Driver(Context &context) : Driver{context, "Smt2Driver"} {}

bool Smt2Driver::ParseStreamCore(std::istream &in) {
  Smt2Scanner scanner(&in);
  scanner.set_debug(debug_scanning_);
  scanner_ = &scanner;

  Smt2Parser parser(*this);
  parser.set_debug_level(debug_parsing_);
  const bool res = parser.parse() == 0;
  scanner_ = nullptr;
  return res;
}

void Smt2Driver::error(const location &l, const std::string &m) { std::cerr << l << " : " << m << std::endl; }

Formula Smt2Driver::EliminateBooleanVariables(const Variables &vars, const Formula &f) {
  Formula ret{f};
  for (const Variable &b : vars) {
    if (b.get_type() == Variable::Type::BOOLEAN) {
      ret = ret.Substitute(b, Formula::True()) && ret.Substitute(b, Formula::False());
    }
  }
  return ret;
}

void Smt2Driver::DefineFun(const std::string &name, const std::vector<Variable> &parameters, Sort return_type,
                           const Term &body) {
  FunctionDefinition func{parameters, return_type, body};
  scope_functions_.insert(name, func);
}

Variable Smt2Driver::RegisterVariable(const std::string &name, const Sort sort) {
  const Variable v{name, SortToType(sort)};
  scope_variables_.insert(v.get_name(), v);
  return v;
}

Variable Smt2Driver::DeclareVariable(const std::string &name, const Sort sort) {
  Variable v{RegisterVariable(name, sort)};
  context_.DeclareVariable(v);
  return v;
}

void Smt2Driver::DeclareVariable(const std::string &name, const Sort sort, const Term &lb, const Term &ub) {
  const Variable v{RegisterVariable(name, sort)};
  context_.DeclareVariable(v, lb.expression(), ub.expression());
}

std::string Smt2Driver::MakeUniqueName(const std::string &name) {
  std::stringstream oss;
  // The \ character ensures that the name cannot occur in an SMT-LIBv2 file.
  oss << "L" << nextUniqueId_++ << "\\" << name;
  return oss.str();
}

Variable Smt2Driver::DeclareLocalVariable(const std::string &name, const Sort sort) {
  const Variable v{MakeUniqueName(name), SortToType(sort)};
  scope_variables_.insert(name, v);  // v is not inserted under its own name.
  context_.DeclareVariable(v, false /* This local variable is not a model variable. */);
  return v;
}

void Smt2Driver::GetValue(const std::vector<Term> &term_list) const {
  const Box &box{context_.model()};
  if (!context_.config().silent()) std::cout << "(\n" << std::endl;
  for (const auto &term : term_list) {
    std::string term_str;
    std::string value_str;
    std::stringstream ss;
    PrefixPrinter pp{ss};

    switch (term.type()) {
      case Term::Type::EXPRESSION: {
        const Expression &e{term.expression()};
        const ExpressionEvaluator evaluator{e};
        pp.Print(e);
        term_str = ss.str();
        const Interval iv{ExpressionEvaluator(term.expression())(box)};
        value_str = (std::stringstream{} << iv).str();
        break;
      }
      case Term::Type::FORMULA: {
        const Formula &f{term.formula()};
        pp.Print(f);
        term_str = ss.str();
        if (is_variable(f)) {
          value_str = box[get_variable(f)].ub() == 1 ? "true" : "false";
        } else {
          DLINEAR_RUNTIME_ERROR_FMT("get-value does not handle a compound formula {}.", term_str);
        }
        break;
      }
    }
    if (!context_.config().silent()) std::cout << "\t(" << term_str << " " << value_str << " )\n";
  }
  if (!context_.config().silent()) std::cout << ")" << std::endl;
}

std::variant<const Expression *, const Variable *> Smt2Driver::LookupDefinedName(const std::string &name) const {
  const auto it = scope_variables_.find(name);
  if (it != scope_variables_.cend()) return {&it->second};
  const auto it2 = scope_constants_.find(name);
  if (it2 != scope_constants_.cend()) return {&it2->second};
  DLINEAR_OUT_OF_RANGE_FMT("{} is an undeclared name.", name);
}

const Expression &Smt2Driver::LookupConstant(const std::string &name) const {
  const auto it = scope_constants_.find(name);
  if (it == scope_constants_.cend()) DLINEAR_OUT_OF_RANGE_FMT("{} is an undeclared constant.", name);
  return it->second;
}

const Variable &Smt2Driver::LookupVariable(const std::string &name) const {
  const auto it = scope_variables_.find(name);
  if (it == scope_variables_.cend()) DLINEAR_OUT_OF_RANGE_FMT("{} is an undeclared variable.", name);
  return it->second;
}

Term Smt2Driver::LookupFunction(const std::string &name, const std::vector<Term> &arguments) const {
  const auto it = scope_functions_.find(name);
  if (it == scope_functions_.end()) DLINEAR_OUT_OF_RANGE_FMT("Function {} is not defined.", name);
  return it->second(arguments);
}

void Smt2Driver::DefineLocalConstant(const std::string &name, const Expression &value) {
  DLINEAR_ASSERT(is_constant(value), "Value must be a constant expression.");
  scope_constants_.insert(name, value);
}

}  // namespace dlinear::smt2
