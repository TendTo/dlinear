/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * This is the header file that we consolidate Drake's symbolic
 * classes and expose them inside of dlinear namespace.
 *
 * Other files in dlinear should include this file and should NOT
 * include files in drake/common directory. Similarly, BUILD files
 * should only have a dependency "//dlinear/symbolic:symbolic", not
 * "@drake_symbolic//:symbolic".
 */
#pragma once

#include <functional>
#include <ostream>
#include <set>
#include <string>
#include <vector>

// From drake
// IWYU pragma: begin_exports
#include "dlinear/symbolic/symbolic_environment.h"
#include "dlinear/symbolic/symbolic_expression.h"
#include "dlinear/symbolic/symbolic_expression_cell.h"
#include "dlinear/symbolic/symbolic_expression_visitor.h"
#include "dlinear/symbolic/symbolic_formula.h"
#include "dlinear/symbolic/symbolic_formula_visitor.h"
#include "dlinear/symbolic/symbolic_variables.h"
// IWYU pragma: end_exports

// From dlinear
#include "dlinear/symbolic/hash.h"
#include "dlinear/symbolic/literal.h"

namespace dlinear {

using drake::symbolic::Environment;
using drake::symbolic::Expression;
using drake::symbolic::ExpressionAddFactory;
using drake::symbolic::ExpressionKind;
using drake::symbolic::Formula;
using drake::symbolic::FormulaKind;
using drake::symbolic::Variables;
using drake::symbolic::VisitExpression;
using drake::symbolic::VisitFormula;

/**
 * Change the kind of the formula by multiplying all the expressions by a negative number.
 *
 * In practice this inverts the inequality from @f$ < @f$ to @f$ > @f$ and @f$ \leq @f$ to @f$ \geq @f$ and vice versa.
 * @param kind kind of the formula
 * @return the negated kind
 */
FormulaKind operator-(FormulaKind kind);

/** Return a formula @p f1 ⇒ @p f2. */
Formula imply(const Formula &f1, const Formula &f2);
/** Return a formula @p v ⇒ @p f. */
Formula imply(const Variable &v, const Formula &f);
/** Return a formula @p f ⇒ @p v. */
Formula imply(const Formula &f, const Variable &v);
/** Return a formula @p v1 ⇒ @p v2. */
Formula imply(const Variable &v1, const Variable &v2);

/** Return a formula @p f1 ⇔ @p f2. */
Formula iff(const Formula &f1, const Formula &f2);
/** Return a formula @p v ⇔ @p f. */
Formula iff(const Variable &v, const Formula &f);
/** Return a formula @p f ⇔ @p v. */
Formula iff(const Formula &f, const Variable &v);
/** Return a formula @p v1 ⇔ @p v2. */
Formula iff(const Variable &v1, const Variable &v2);

/**
 * Given @p formulas = {f₁, ..., fₙ} and a @p func : Formula → Formula,
 * `map(formulas, func)` returns a set `{func(f₁), ... func(fₙ)}`.
 * @param formulas set of formulas
 * @param func function to apply to each formula
 * @return set of formulas obtained by applying @p func to each formula in
 */
std::set<Formula> map(const std::set<Formula> &formulas, const std::function<Formula(const Formula &)> &func);

/**
 * Check if @p f is atomic.
 * @param f formula to check
 * @return whether @p f is atomic
 */
bool is_atomic(const Formula &f);

/**
 * Check if @p f is a clause.
 * A clause is a disjunction of literals.
 * @param f formula to check
 * @return whether @p f is a clause
 */
bool is_clause(const Formula &f);

/**
 * Returns the set of clauses in f.
 * F is assumed to be in CNF. That is, f is either a single clause or a
 * conjunction of clauses.
 * @param f formula to get clauses from
 * @return set of clauses in @p f
 */
std::set<Formula> get_clauses(const Formula &f);

/**
 * Check if @p f is in CNF form.
 * @param f formula to check
 * @return whether @p f is in CNF form
 */
bool is_cnf(const Formula &f);

/**
 * Check if the intersection of @p variables1 and @p variables2 is
 * non-empty.
 * @param variables1 set of variables
 * @param variables2 set of variables
 * @return true if @p variables1 and @p variables2 is an non-empty
 * intersection.
 */
bool HaveIntersection(const Variables &variables1, const Variables &variables2);

/**
 * Strengthen the input formula @p f by @p delta.
 * @param f formula to strengthen
 * @param delta amount to strengthen by
 * @return strengthened formula
 */
Formula DeltaStrengthen(const Formula &f, double delta);

/**
 * Weaken the input formula @p f by @p delta.
 * @param f formula to weaken
 * @param delta amount to weaken by
 * @return weakened formula
 */
Formula DeltaWeaken(const Formula &f, double delta);

/**
 * Check if the formula @p f is symbolic-differentiable.
 * @param f formula to check
 * @return true if @p f is symbolic-differentiable
 */
bool IsDifferentiable(const Formula &f);

/**
 * Check if the expression @e f is symbolic-differentiable.
 * @param e expression to check
 * @return true if @p e is symbolic-differentiable
 */
bool IsDifferentiable(const Expression &e);

/**
 * Make conjunction of @p formulas.
 * @note This is different from the one in Drake's symbolic
 * library. It takes `std::vector<Formula>` while Drake's version
 * takes `std::set<Formula>`.
 * @param formulas input formulas
 * @return conjunction of @p formulas
 */
Formula make_conjunction(const std::vector<Formula> &formulas);

/**
 * Make disjunction of @p formulas.
 * @note This is different from the one in Drake's symbolic
 * library. It takes `std::vector<Formula>` while Drake's version
 * takes `std::set<Formula>`.
 * @param formulas input formulas
 * @return disjunction of @p formulas
 */
Formula make_disjunction(const std::vector<Formula> &formulas);

/**
 * Creates a vector of variables of @p type whose size is @p size.
 * The variables are numbered with @p prefix. For example
 * @code
 * CreateVector("x", 5) // returns [x0, x1, x2, x3, x4]
 * @endcode
 * @param prefix prefix of variable names. Must not be empty.
 * @param size size of vector. Must be >= 1.
 * @param type type of variables
 * @return vector of variables
 */
std::vector<Variable> CreateVector(const std::string &prefix, int size,
                                   Variable::Type type = Variable::Type::CONTINUOUS);

/** Relational operators are used in formulas */
enum class RelationalOperator {
  EQ,   ///< =
  NEQ,  ///< !=
  GT,   ///< >
  GEQ,  ///< >=
  LT,   ///< <
  LEQ,  ///< <=
};

/**
 * Negates @p op.
 * @param op operator to negate
 * @return negated operator
 */
RelationalOperator operator!(RelationalOperator op);

std::ostream &operator<<(std::ostream &os, RelationalOperator op);

std::ostream &operator<<(std::ostream &os, const FormulaKind &kind);

std::ostream &operator<<(std::ostream &os, const ExpressionKind &kind);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::Expression)
OSTREAM_FORMATTER(dlinear::Formula)
OSTREAM_FORMATTER(dlinear::Variables)
OSTREAM_FORMATTER(dlinear::RelationalOperator)
OSTREAM_FORMATTER(dlinear::FormulaKind)
OSTREAM_FORMATTER(dlinear::ExpressionKind)

#endif
