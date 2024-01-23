/**
 * @file Term.h
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 * @brief Term obtained by parsing the SMT2 file.
 *
 * Terms are the building blocks of a smt problem. They are either
 * expressions or formulas.
 */
#pragma once

#include <iostream>

#include "dlinear/symbolic/symbolic.h"

/// Sum type of symbolic::Expression and symbolic::Formula.
namespace dlinear::smt2 {

class Term {
 public:
  enum class Type { EXPRESSION, FORMULA };

  /**
   * Construct a term with @p e.
   * @param e expression to construct a term with
   */
  explicit Term(Expression e);

  /**
   * Construct a term with @p f.
   * @param f formula to construct a term with
   */
  explicit Term(Formula f);

  /** Default copy constructor. */
  Term(const Term &) = default;

  /** Default move constructor. */
  Term(Term &&) = default;

  /** Default copy assign operator. */
  Term &operator=(const Term &) = default;

  /** Default move assign operator. */
  Term &operator=(Term &&) = default;

  /** Default destructor. */
  ~Term() = default;

  /** Return the type of this term. */
  Type type() const;

  /**
   * Return the expression inside.
   * @return constant reference expression inside
   * @throw runtime_error if it does not include an expression
   */
  const Expression &expression() const;

  /**
   * Return the expression inside.
   * @return mutable reference to the expression inside
   * @throw runtime_error if it does not include an expression
   */
  Expression &m_expression();

  /**
   * Return the formula inside.
   * @return constant reference to the formula inside
   * @throw runtime_error if it does not include a formula
   */
  const Formula &formula() const;

  /**
   * Return the formula inside.
   * @return mutable reference to the formula inside
   * @throw runtime_error if it does not include a formula
   */
  Formula &m_formula();

 private:
  Type type_;     ///< Type of this term.
  Expression e_;  ///< Expression inside.
  Formula f_;     ///< Formula inside.
};

std::ostream &operator<<(std::ostream &os, const Term &t);
}  // namespace dlinear::smt2
