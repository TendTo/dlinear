/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "Term.h"

#include <iostream>

#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear::vnnlib {

Term::Term() : term_{} {}
Term::Term(Expression e) : term_{e} { DLINEAR_TRACE_FMT("Term::Term({}) - Expression", e); }
Term::Term(Formula f) : term_{f} { DLINEAR_TRACE_FMT("Term::Term({}) - Formula", f); }
Term &Term::operator=(const Formula &f) {
  term_.emplace<Formula>(f);
  return *this;
}
Term &Term::operator=(const Expression &e) {
  term_.emplace<Expression>(e);
  return *this;
}
Term &Term::operator=(Formula &&f) {
  term_.emplace<Formula>(f);
  return *this;
}
Term &Term::operator=(Expression &&e) {
  term_.emplace<Expression>(e);
  return *this;
}

Term::Type Term::type() const { return std::holds_alternative<Expression>(term_) ? Type::EXPRESSION : Type::FORMULA; }
const Expression &Term::expression() const { return std::get<Expression>(term_); }
Expression &Term::m_expression() { return std::get<Expression>(term_); }
const Formula &Term::formula() const { return std::get<Formula>(term_); }
Formula &Term::m_formula() { return std::get<Formula>(term_); }

Term Term::Substitute(const Variable &v, const Term &t) {
  switch (type()) {
    case Type::FORMULA: {
      switch (v.get_type()) {
        case Variable::Type::CONTINUOUS:
        case Variable::Type::INTEGER:
        case Variable::Type::BINARY:
          return Term{formula().Substitute(v, t.expression())};
        case Variable::Type::BOOLEAN:
          return Term{formula().Substitute(v, t.formula())};
        default:
          DLINEAR_UNREACHABLE();
      }
    }
    case Type::EXPRESSION: {
      switch (v.get_type()) {
        case Variable::Type::CONTINUOUS:
        case Variable::Type::INTEGER:
        case Variable::Type::BINARY:
          return Term{expression().Substitute(v, t.expression())};
        case Variable::Type::BOOLEAN:
          return Term{expression().Substitute({}, {{v, t.formula()}})};
        default:
          DLINEAR_UNREACHABLE();
      }
    }
    default:
      DLINEAR_UNREACHABLE();
  }
}

void Term::Check(Sort s) const {
  switch (type()) {
    case Term::Type::EXPRESSION:
      if (s == Sort::Int || s == Sort::Real || s == Sort::Binary) return;  // OK
      break;
    case Term::Type::FORMULA:
      if (s == Sort::Bool) return;  // OK
      break;
    default:
      DLINEAR_RUNTIME_ERROR_FMT("Term {} does not match against sort {}", *this, s);
  }
}

void Term::Check(Variable::Type t) const {
  switch (type()) {
    case Type::FORMULA:
      if (t == Variable::Type::BOOLEAN) return;  // OK
      break;
    case Type::EXPRESSION:
      if (t == Variable::Type::BINARY || t == Variable::Type::INTEGER || t == Variable::Type::CONTINUOUS) return;  // OK
      break;
    default:
      DLINEAR_RUNTIME_ERROR_FMT("Term {} does not match against type {}", *this, t);
  }
}

std::ostream &operator<<(std::ostream &os, const Term &t) {
  switch (t.type()) {
    case Term::Type::EXPRESSION:
      return os << t.expression();
    case Term::Type::FORMULA:
      return os << t.formula();
    default:
      DLINEAR_UNREACHABLE();
  }
}

}  // namespace dlinear::vnnlib
