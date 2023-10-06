#pragma once

#include <memory>

#include "dlinear/libs/gmp.h"
#include "dlinear/symbolic/Environment.h"
#include "dlinear/symbolic/Variable.h"
#include "dlinear/symbolic/Variables.h"

namespace dlinear::symbolic {

/** Kinds of symbolic expressions. */
enum class ExpressionKind {
  Constant,               ///< rational constant (mpq_class)
  Var,                    ///< variable
  Add,                    ///< addition (+)
  Mul,                    ///< multiplication (*)
  Div,                    ///< division (/)
  Log,                    ///< logarithms
  Abs,                    ///< absolute value function
  Exp,                    ///< exponentiation
  Sqrt,                   ///< square root
  Pow,                    ///< power function
  Sin,                    ///< sine
  Cos,                    ///< cosine
  Tan,                    ///< tangent
  Asin,                   ///< arcsine
  Acos,                   ///< arccosine
  Atan,                   ///< arctangent
  Atan2,                  ///< arctangent2 (atan2(y,x) = atan(y/x))
  Sinh,                   ///< hyperbolic sine
  Cosh,                   ///< hyperbolic cosine
  Tanh,                   ///< hyperbolic tangent
  Min,                    ///< min
  Max,                    ///< max
  IfThenElse,             ///< if then else
  NaN,                    ///< NaN
  Infty,                  ///< infinity
  UninterpretedFunction,  ///< Uninterpreted function
  // TODO(soonho): add Integral
};

/** Total ordering between ExpressionKinds. */
bool operator<(ExpressionKind k1, ExpressionKind k2);

#if 1

class ExpressionCell;                   // In symbolic_expression_cell.h
class ExpressionConstant;               // In symbolic_expression_cell.h
class ExpressionInfty;                  // In symbolic_expression_cell.h
class ExpressionVar;                    // In symbolic_expression_cell.h
class UnaryExpressionCell;              // In symbolic_expression_cell.h
class BinaryExpressionCell;             // In symbolic_expression_cell.h
class ExpressionAdd;                    // In symbolic_expression_cell.h
class ExpressionMul;                    // In symbolic_expression_cell.h
class ExpressionDiv;                    // In symbolic_expression_cell.h
class ExpressionLog;                    // In symbolic_expression_cell.h
class ExpressionAbs;                    // In symbolic_expression_cell.h
class ExpressionExp;                    // In symbolic_expression_cell.h
class ExpressionSqrt;                   // In symbolic_expression_cell.h
class ExpressionPow;                    // In symbolic_expression_cell.h
class ExpressionSin;                    // In symbolic_expression_cell.h
class ExpressionCos;                    // In symbolic_expression_cell.h
class ExpressionTan;                    // In symbolic_expression_cell.h
class ExpressionAsin;                   // In symbolic_expression_cell.h
class ExpressionAcos;                   // In symbolic_expression_cell.h
class ExpressionAtan;                   // In symbolic_expression_cell.h
class ExpressionAtan2;                  // In symbolic_expression_cell.h
class ExpressionSinh;                   // In symbolic_expression_cell.h
class ExpressionCosh;                   // In symbolic_expression_cell.h
class ExpressionTanh;                   // In symbolic_expression_cell.h
class ExpressionMin;                    // In symbolic_expression_cell.h
class ExpressionMax;                    // In symbolic_expression_cell.h
class ExpressionIfThenElse;             // In symbolic_expression_cell.h
class ExpressionUninterpretedFunction;  // In symbolic_expression_cell.h
class Formula;                          // In symbolic_formula.h
class Expression;

// ExpressionSubstitution is a map from a Variable to a symbolic expression. It
// is used in Expression::Substitute and Formula::Substitute methods as an
// argument.
using ExpressionSubstitution = std::unordered_map<Variable, Expression>;

// FormulaSubstitution is a map from a Variable to a symbolic formula. It
// is used in Expression::Substitute and Formula::Substitute methods as an
// argument.
using FormulaSubstitution = std::unordered_map<Variable, Formula>;

/**
 * Represents a symbolic form of an expression.
 *
 * Its syntax tree is as follows:
 *
 * @verbatim
 *     E := Var | Constant(mpq_class)
 *        | E + ... + E | E * ... * E | E / E | log(E)
 *        | abs(E) | exp(E) | sqrt(E) | pow(E, E) | sin(E) | cos(E) | tan(E)
 *        | asin(E) | acos(E) | atan(E) | atan2(E, E) | sinh(E) | cosh(E)
 *        | tanh(E) | min(E, E) | max(E, E) | if_then_else(F, E, E) | NaN
 *        | infinity | uninterpreted_function(name, {v_1, ..., v_n})
 * @endverbatim
 *
 * In the implementation, Expression is a simple wrapper including a
 * pointer to ExpressionCell class which is a super-class of different
 * kinds of symbolic expressions (i.e. ExpressionAdd, ExpressionMul,
 * ExpressionLog, ExpressionSin).
 *
 * @note The sharing of sub-expressions is not yet implemented.
 *
 * @note -E is represented as -1 * E internally.
 *
 * @note A subtraction E1 - E2 is represented as E1 + (-1 * E2) internally.
 *
 * The following simple simplifications are implemented:
 * @verbatim
 *     E + 0             ->  E
 *     0 + E             ->  E
 *     E - 0             ->  E
 *     E - E             ->  0
 *     E * 1             ->  E
 *     1 * E             ->  E
 *     E * 0             ->  0
 *     0 * E             ->  0
 *     E / 1             ->  E
 *     E / E             ->  1
 *     pow(E, 0)         ->  1
 *     pow(E, 1)         ->  E
 *     E * E             ->  E^2 (= pow(E, 2))
 *     sqrt(E * E)       ->  |E| (= abs(E))
 *     sqrt(E) * sqrt(E) -> E
 * @endverbatim
 *
 * Constant folding is implemented:
 * @verbatim
 *     E(c1) + E(c2)  ->  E(c1 + c2)    // c1, c2 are constants
 *     E(c1) - E(c2)  ->  E(c1 - c2)
 *     E(c1) * E(c2)  ->  E(c1 * c2)
 *     E(c1) / E(c2)  ->  E(c1 / c2)
 *     f(E(c))        ->  E(f(c))       // c is a constant, f is a math function
 * @endverbatim
 *
 * For the math functions which are only defined over a restricted domain
 * (namely, log, sqrt, pow, asin, acos), we check the domain of argument(s), and
 * throw std::domain_error exception if a function is not well-defined for a
 * given argument(s).
 *
 * Relational operators over expressions (==, !=, <, >, <=, >=) return
 * symbolic::Formula instead of bool. Those operations are declared in
 * symbolic_formula.h file. To check structural equality between two expressions
 * a separate function, Expression::EqualTo, is provided.
 */
class Expression {
 public:
  Expression(const Expression &);
  Expression &operator=(const Expression &);
  Expression(Expression &&) noexcept;
  Expression &operator=(Expression &&) noexcept;
  ~Expression();

  /** Default constructor. It constructs Zero(). */
  Expression();

  /** Constructs a constant (rational). */
  // NOLINTNEXTLINE(runtime/explicit): This conversion is desirable.
  Expression(const mpq_class &d);
  // NOLINTNEXTLINE(runtime/explicit): This conversion is desirable.
  Expression(const double d);
  /** Constructs an expression from @p var.
   * @pre @p var is neither a dummy nor a BOOLEAN variable.
   */
  // NOLINTNEXTLINE(runtime/explicit): This conversion is desirable.
  Expression(const Variable &var);
  /** Returns expression kind. */
  ExpressionKind get_kind() const;
  /** Returns hash value. */
  size_t get_hash() const;
  /** Collects variables in expression. */
  const Variables &GetVariables() const;

  /** Checks structural equality.
   *
   * Two expressions e1 and e2 are structurally equal when they have the same
   * internal AST(abstract-syntax tree) representation. Please note that we can
   * have two computationally (or extensionally) equivalent expressions which
   * are not structurally equal. For example, consider:
   *
   *    e1 = 2 * (x + y)
   *    e2 = 2x + 2y
   *
   * Obviously, we know that e1 and e2 are evaluated to the same value for all
   * assignments to x and y. However, e1 and e2 are not structurally equal by
   * the definition. Note that e1 is a multiplication expression
   * (is_multiplication(e1) is true) while e2 is an addition expression
   * (is_addition(e2) is true).
   *
   * One main reason we use structural equality in EqualTo is due to
   * Richardson's Theorem. It states that checking ∀x. E(x) = F(x) is
   * undecidable when we allow sin, asin, log, exp in E and F. Read
   * https://en.wikipedia.org/wiki/Richardson%27s_theorem for details.
   *
   * Note that for polynomial cases, you can use Expand method and check if two
   * polynomial expressions p1 and p2 are computationally equal. To do so, you
   * check the following:
   *
   *     (p1.Expand() - p2.Expand()).EqualTo(0).
   */
  bool EqualTo(const Expression &e) const;

  /** Provides lexicographical ordering between expressions.
      This function is used as a compare function in map<Expression> and
      set<Expression> via std::less<dlinear::drake::symbolic::Expression>. */
  bool Less(const Expression &e) const;

  /** Checks if this symbolic expression is convertible to Polynomial. */
  bool is_polynomial() const;

  /// Returns true if this symbolic expression includes an ITE (If-Then-Else)
  /// expression.
  bool include_ite() const;

  /** Evaluates under a given environment (by default, an empty environment).
   *  @throws std::runtime_error if NaN is detected during evaluation.
   */
  mpq_class Evaluate(const Environment &env = Environment{}) const;

  /** Partially evaluates this expression using an environment @p
   * env. Internally, this method promotes @p env into a substitution
   * (Variable → Expression) and call Evaluate::Substitute with it.
   *
   * @throws std::runtime_error if NaN is detected during evaluation.
   */
  Expression EvaluatePartial(const Environment &env) const;

  /** Expands out products and positive integer powers in expression. For
   * example, `(x + 1) * (x - 1)` is expanded to `x^2 - 1` and `(x + y)^2` is
   * expanded to `x^2 + 2xy + y^2`. Note that Expand applies recursively to
   * sub-expressions. For instance, `sin(2 * (x + y))` is expanded to `sin(2x +
   * 2y)`. It also simplifies "division by constant" cases. See
   * "symbolic/test/symbolic_expansion_test.cc" to find the examples.
   *
   * @throws std::runtime_error if NaN is detected during expansion.
   */
  Expression Expand() const;

  /** Returns a copy of this expression replacing all occurrences of @p var
   * with @p e.
   * @throws std::runtime_error if NaN is detected during substitution.
   */
  Expression Substitute(const Variable &var, const Expression &e) const;

  /** Returns a copy of this expression replacing all occurrences of the
   * variables in @p expr_subst with corresponding expressions in @p expr_subst
   * and all occurrences of the variables in @p formula_subst with corresponding
   * formulas in @p formula_subst.
   *
   * Note that the substitutions occur simultaneously. For example,
   * (x / y).Substitute({{x, y}, {y, x}}, {}) gets (y / x).
   *
   * @throws std::runtime_error if NaN is detected during substitution.
   */
  Expression Substitute(const ExpressionSubstitution &expr_subst, const FormulaSubstitution &formula_subst) const;

  /** Returns a copy of this expression replacing all occurrences of the
   * variables in @p expr_subst with corresponding expressions in @p expr_subst.
   *
   * @note This is equivalent to `Substitute(expr_subst, {})`.
   * @throws std::runtime_error if NaN is detected during substitution.
   */
  Expression Substitute(const ExpressionSubstitution &expr_subst) const;

  /** Returns a copy of this expression replacing all occurrences of the
   * variables in @p formula_subst with corresponding formulas in @p
   * formula_subst.
   *
   * @note This is equivalent to `Substitute({}, formula_subst)`.
   * @throws std::runtime_error if NaN is detected during substitution.
   */
  Expression Substitute(const FormulaSubstitution &formula_subst) const;

  /** Differentiates this symbolic expression with respect to the variable @p
   * var.
   * @throws std::runtime_error if it is not differentiable.
   */
  Expression Differentiate(const Variable &x) const;

  /** Returns string representation of Expression. */
  std::string to_string() const;

  /** Returns zero. */
  static Expression Zero();
  /** Returns one. */
  static Expression One();
  /** Returns Pi, the ratio of a circle’s circumference to its diameter. */
  static Expression Pi();
  /** Return e, the base of natural logarithms. */
  static Expression E();
  /** Returns NaN (Not-a-Number). */
  static Expression NaN();
  /** Returns positive infinity. */
  static Expression Infty();
  /** Returns negative infinity. */
  static Expression NInfty();

  friend Expression operator+(const Expression &lhs, const Expression &rhs);
  friend Expression operator+(const Expression &lhs, Expression &&rhs);
  friend Expression operator+(Expression &&lhs, const Expression &rhs);
  friend Expression operator+(Expression &&lhs, Expression &&rhs);
  // NOLINTNEXTLINE(runtime/references) per C++ standard signature.
  friend Expression &operator+=(Expression &lhs, const Expression &rhs);

  /** Provides prefix increment operator (i.e. ++x). */
  Expression &operator++();
  /** Provides postfix increment operator (i.e. x++). */
  Expression operator++(int);

  friend Expression operator-(const Expression &lhs, const Expression &rhs);
  friend Expression operator-(const Expression &lhs, Expression &&rhs);
  friend Expression operator-(Expression &&lhs, const Expression &rhs);
  friend Expression operator-(Expression &&lhs, Expression &&rhs);
  // NOLINTNEXTLINE(runtime/references) per C++ standard signature.
  friend Expression &operator-=(Expression &lhs, const Expression &rhs);

  /** Provides unary plus operator. */
  friend Expression operator+(const Expression &e);

  /** Provides unary minus operator. */
  friend Expression operator-(const Expression &e);
  friend Expression operator-(Expression &&e);

  /** Provides prefix decrement operator (i.e. --x). */
  Expression &operator--();
  /** Provides postfix decrement operator (i.e. x--). */
  Expression operator--(int);

  friend Expression operator*(const Expression &lhs, const Expression &rhs);
  friend Expression operator*(const Expression &lhs, Expression &&rhs);
  friend Expression operator*(Expression &&lhs, const Expression &rhs);
  friend Expression operator*(Expression &&lhs, Expression &&rhs);
  // NOLINTNEXTLINE(runtime/references) per C++ standard signature.
  friend Expression &operator*=(Expression &lhs, const Expression &rhs);

  friend Expression operator/(Expression lhs, const Expression &rhs);
  // NOLINTNEXTLINE(runtime/references) per C++ standard signature.
  friend Expression &operator/=(Expression &lhs, const Expression &rhs);

  friend class ExpressionCell;

 private:
  Expression(ExpressionCell *cell);
  ExpressionCell *cell_{};
};
#endif
}  // namespace dlinear::symbolic