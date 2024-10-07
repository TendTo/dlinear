/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Term class.
 *
 * Terms are the building blocks of a smt problem.
 * They can take many forms, such as:
 * - variables
 * - constants
 * - functions
 */
#pragma once

#include <iosfwd>
#include <variant>

#include "dlinear/parser/vnnlib/Sort.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear::vnnlib {

/**
 * Generic term that can be either an expression or a formula.
 *
 * It is used to store the parsed term from the VNNLIB file.
 * They can take many forms, such as:
 * - variables
 * - constants
 * - functions
 */
class Term {
 public:
  enum class Type { EXPRESSION, FORMULA };

  /** @constructor{term} */
  Term();
  ~Term() = default;
  /**
   * Construct a term with the expression @p e.
   * @param e expression to construct a term with
   */
  explicit Term(Expression e);
  /**
   * Construct a term with the formula @p f.
   * @param f formula to construct a term with
   */
  explicit Term(Formula f);
  Term(const Term &) = default;
  Term(Term &&) = default;
  Term &operator=(const Term &) = default;
  Term &operator=(const Formula &);
  Term &operator=(const Expression &);
  Term &operator=(Term &&) = default;
  Term &operator=(Formula &&);
  Term &operator=(Expression &&);

  /** @getter{type, term} */
  [[nodiscard]] Type type() const;
  /** @getter{expression, term, @throw std::std::bad_variant_access if it does not include a expression} */
  [[nodiscard]] const Expression &expression() const;
  /** @getsetter{expression, term, @throw std::std::bad_variant_access if it does not include a expression} */
  Expression &m_expression();
  /** @getter{formula, term, @throw std::std::bad_variant_access if it does not include a formula} */
  [[nodiscard]] const Formula &formula() const;
  /** @getsetter{formula, term, @throw std::std::bad_variant_access if it does not include a formula} */
  Formula &m_formula();

  /**
   * Create a new Term with substitutes the variable @p v in this term with @p t.
   * @param v variable to substitute
   * @param t new term that replaces the variable
   * @return new term with the substitution
   */
  Term Substitute(const Variable &v, const Term &t);

  /**
   * Check if this term can be matched with @p s.
   * @param s sort to match with
   * @throw std::runtime_error if @p s is mismatched
   */
  void Check(Sort s) const;

  /**
   * Check if this term can be matched with @p t.
   * @param t type of the variable
   * @throw std::runtime_error if @p t is mismatched
   */
  void Check(Variable::Type t) const;

 private:
  std::variant<Expression, Formula> term_;  ///< Expression or formula stored by the term
};

std::ostream &operator<<(std::ostream &os, const Term &t);

}  // namespace dlinear::vnnlib

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::vnnlib::Term)

#endif
