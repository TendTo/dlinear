#pragma once

#include "dlinear/symbolic/Environment.h"
#include "dlinear/symbolic/Expression.h"
#include "dlinear/symbolic/Variable.h"
#include "dlinear/symbolic/Variables.h"

namespace dlinear::symbolic {

class ExpressionCell {
 public:
  /** Returns expression kind. */
  ExpressionKind get_kind() const { return kind_; }

  /** Returns hash value. */
  std::size_t get_hash() const { return hash_; }

  /** Collects variables in expression. */
  const Variables &GetVariables() const { return variables_; }

  /** Checks structural equality. */
  virtual bool EqualTo(const ExpressionCell &c) const = 0;

  /** Provides lexicographical ordering between expressions. */
  virtual bool Less(const ExpressionCell &c) const = 0;

  /** Checks if this symbolic expression is convertible to Polynomial. */
  bool is_polynomial() const { return is_polynomial_; }

  /// Returns true if this symbolic expression includes an ITE (If-Then-Else)
  /// expression.
  bool include_ite() const { return include_ite_; }

  /** Evaluates under a given environment (by default, an empty environment).
   *  @throws std::runtime_error if NaN is detected during evaluation.
   */
  virtual mpq_class Evaluate(const Environment &env) const = 0;

  /** Expands out products and positive integer powers in expression.
   * @throws std::runtime_error if NaN is detected during expansion.
   */
  virtual Expression Expand() = 0;

  /**
   * Returns an Expression obtained by replacing all occurrences of the
   * variables in @p s in the current expression cell with the corresponding
   * expressions in @p s.
   * @throws std::runtime_error if NaN is detected during substitution.
   */
  virtual Expression Substitute(const ExpressionSubstitution &expr_subst, const FormulaSubstitution &formula_subst) = 0;

  /**
   * Differentiates this symbolic expression with respect to the variable @p
   * var.
   * @throws std::runtime_error if it is not differentiable.
   */
  virtual Expression Differentiate(const Variable &x) const = 0;

  /** Outputs string representation of expression into output stream @p os. */
  virtual std::ostream &Display(std::ostream &os) const = 0;

  /** Copy-constructs an ExpressionCell from an lvalue. (DELETED) */
  ExpressionCell(const ExpressionCell &e) = delete;

  /** Move-constructs an ExpressionCell from an rvalue. (DELETED) */
  ExpressionCell(ExpressionCell &&e) = delete;

  /** Move-assigns (DELETED). */
  ExpressionCell &operator=(ExpressionCell &&e) = delete;

  /** Copy-assigns (DELETED). */
  ExpressionCell &operator=(const ExpressionCell &e) = delete;

 protected:
  /** Default constructor. */
  ExpressionCell() = default;
  /** Constructs ExpressionCell of kind @p k with @p hash, @p is_poly, and @p
   * include_ite. */
  ExpressionCell(ExpressionKind k, size_t hash, bool is_poly, bool include_ite, Variables variables);
  /** Default destructor. */
  virtual ~ExpressionCell() = default;
  /** Returns an expression pointing to this ExpressionCell. */
  Expression GetExpression();

 private:
  const ExpressionKind kind_{};
  const size_t hash_{};
  const bool is_polynomial_{false};
  const bool include_ite_{false};
  const Variables variables_;
};

}  // namespace dlinear::symbolic