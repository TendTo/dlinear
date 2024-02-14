/**
 * @file Term.cpp
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 */
#include "Term.h"

#include <stdexcept>
#include <utility>

#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear::smt2 {

Term::Term(Expression e) : type_{Term::Type::EXPRESSION}, e_{std::move(e)} {
  DLINEAR_TRACE_FMT("Term::Term({}) - Expression", e_);
}
Term::Term(Formula f) : type_{Term::Type::FORMULA}, f_{std::move(f)} {
  DLINEAR_TRACE_FMT("Term::Term({}) - Formula", f_);
}

Term::Type Term::type() const { return type_; }

const Expression &Term::expression() const {
  if (type() != Term::Type::EXPRESSION) {
    throw std::runtime_error("This term is not an expression.");
  }
  return e_;
}

Expression &Term::m_expression() { return const_cast<Expression &>(expression()); }

const Formula &Term::formula() const {
  if (type() != Term::Type::FORMULA) {
    throw std::runtime_error("This term is not a formula.");
  }
  return f_;
}

Formula &Term::m_formula() { return const_cast<Formula &>(formula()); }

std::ostream &operator<<(std::ostream &os, const Term &t) {
  switch (t.type()) {
    case Term::Type::EXPRESSION:
      return os << t.expression();
    case Term::Type::FORMULA:
      return os << t.formula();
  }
  DLINEAR_UNREACHABLE();
}

}  // namespace dlinear::smt2
