/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * PiecewiseLinearConstraint class.
 */
#pragma once

#include <istream>
#include <optional>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/BoundPreprocessor.h"
#include "dlinear/solver/PiecewiseConstraintState.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

/**
 * A piecewise linear constraint is a constraint that assumes different linear functions
 * depending on the truth assignment of a literal.
 *
 * This kind of constraints are in the form:
 * @f[
 * y = \begin{cases}
 *  f_\text{active}(x) & \text{if } l \\
 *  f_\text{inactive}(x) & \text{otherwise}
 *  \end{cases}
 *  @f]
 *  where @f$ f_\text{active}, f_\text{inactive} @f$ are linear functions of @f$ x @f$
 *  and @f$ l @f$ is the literal that determines which of the two is assigned to @f$ y @f$.
 *  To prune some trivial cases, the class keeps a bound on the value of @f$ y @f$.
 */
class PiecewiseLinearConstraint {
 public:
  static const Expression zero_soi;  ///< Expression @f$ 0 @f$ used as a soi if the constraint is not fixed yet

  /**
   * Construct a new Piecewise Linear Constraint object
   * @param lb lower bound of the constraint. If not specified, the constraint is unbounded from below (-inf)
   * @param ub upper bound of the constraint. If not specified, the constraint is unbounded from above (+inf)
   * @param active_var boolean variable associated with the @f$ y = f_\text{active}(x) @f$ theory literal
   * @param inactive_var boolean variable associated with the @f$ y = f_\text{inactive}(x) @f$ theory literal
   * @param theory_var theory variable @f$ y @f$
   * @param active_soi expression @f$ y - f_\text{active}(x) @f$
   * @param inactive_soi expression @f$ y - f_\text{inactive}(x) @f$
   * @param state state of the constraint
   */
  explicit PiecewiseLinearConstraint(const mpq_class* lb = nullptr, const mpq_class* ub = nullptr,
                                     Variable active_var = {}, Variable inactive_var = {}, Variable theory_var = {},
                                     Expression active_soi = {0}, Expression inactive_soi = {0},
                                     PiecewiseConstraintState state = PiecewiseConstraintState::NOT_FIXED);
  virtual ~PiecewiseLinearConstraint() = default;

  /**
   * Use the @p preprocessor to tighten the bounds of the constraint and hopefully fix its state to either
   * active or inactive.
   * @param preprocessor preprocessor to use to tighten the bounds
   * @return explanation of why the inactive state of this constraint is unsat
   */
  virtual std::set<LiteralSet> TightenBounds(BoundPreprocessor& preprocessor) = 0;

  /**
   * Print the constraint on the standard output
   * @param os standard output
   * @return updated standard output
   */
  virtual std::ostream& Print(std::ostream& os) const = 0;

  /**
   * The assumptions used to guide the SAT solver towards the most promising sub-problems.
   * @return set of literals
   */
  [[nodiscard]] virtual LiteralSet Assumptions() const = 0;
  /**
   * Produce some learned clauses the SAT solver will use to prune the sub-problems
   * this piecewise constraint will not be satisfied in.
   * @return set of literals
   */
  [[nodiscard]] virtual LiteralSet LearnedClauses() const = 0;

  /**
   * Update the bounds of the constraint
   * @pre the new lower bound must be less than or equal to the new upper bound
   * @pre the new lower bound must be greater than or equal to the current lower bound
   * @pre the new upper bound must be less than or equal to the current upper bound
   * @param lb lower bound of the constraint
   * @param ub upper bound of the constraint
   */
  void UpdateBounds(const mpq_class& lb, const mpq_class& ub);
  /**
   * Update the bounds of the constraint
   *
   * If any of the bounds is not specified, the corresponding bound is not updated.
   * @pre the new lower bound must be less than or equal to the new upper bound
   * @pre the new lower bound must be greater than or equal to the current lower bound
   * @pre the new upper bound must be less than or equal to the current upper bound
   * @param lb lower bound of the constraint
   * @param ub upper bound of the constraint
   */
  void UpdateBounds(const mpq_class* lb, const mpq_class* ub);
  /**
   * Update the lower bounds of the constraint
   * @pre the new lower bound must be greater than or equal to the current lower bound
   * @param lb lower bound of the constraint
   */
  virtual void UpdateLowerBound(const mpq_class* lb);
  /**
   * Update the upper bounds of the constraint
   * @pre the new upper bound must be less than or equal to the current upper bound
   * @param ub upper bound of the constraint
   */
  virtual void UpdateUpperBound(const mpq_class* ub);

  /**
   * Calculate the cost of the violation of the constraint.
   *
   * Given a feasible solution of the LP problems where this constraint contributes to the objective function
   * as a Sum Of Infeasibilities, calculate the amount of violation caused by its presence in the current state.
   * If the constraint is not fixed yet, return @f$ 0 @f$.
   * @param env current assignment to all the theory variables
   * @return cost of the violation
   */
  [[nodiscard]] mpq_class Cost(const Environment& env) const;
  /**
   * Calculate the cost of the violation of the constraint forcing a specific state.
   *
   * Given a feasible solution of the LP problems where this constraint contributes to the objective function
   * as a Sum Of Infeasibilities, calculate the amount of violation caused by its presence in the current state.
   * @param env current assignment to all the theory variables
   * @param active whether to consider the constraint as active or inactive
   * @return cost of the violation
   */
  [[nodiscard]] mpq_class Cost(const Environment& env, bool active) const;

  /** @checker{lower bounded, constraint} */
  [[nodiscard]] bool has_lower_bound() const { return lower_bound_ != nullptr; }
  /** @checker{upper bounded, constraint} */
  [[nodiscard]] bool has_upper_bound() const { return upper_bound_ != nullptr; }
  /** @checker{fixed, constraint} */
  [[nodiscard]] bool fixed() const {
    return state_ == PiecewiseConstraintState::ACTIVE || state_ == PiecewiseConstraintState::INACTIVE;
  }
  /** @getter{lower bound, constraint, If the constraint does not have a lower bound, -inf value is returned} */
  [[nodiscard]] const mpq_class& lower_bound() const;
  /** @getter{upper bound, constraint, If the constraint does not have an upper bound, +inf value is returned} */
  [[nodiscard]] const mpq_class& upper_bound() const;
  /** @getter{boolean variable associated with the @f$ y = f_\text{active}(x) @f$ theory literal, constraint} */
  [[nodiscard]] const Variable& active_var() const { return active_var_; }
  /** @getter{boolean variable associated with the @f$ y = f_\text{inactive}(x) @f$ theory literal, constraint} */
  [[nodiscard]] const Variable& inactive_var() const { return inactive_var_; }
  /** @getter{theory variable @f$ y @f$, constraint} */
  [[nodiscard]] const Variable& theory_var() const { return theory_var_; }
  /** @getter{expression @f$ y - f_\text{active}(x) @f$, constraint} */
  [[nodiscard]] const Expression& active_soi() const { return active_soi_; }
  /** @getter{expression @f$ y - f_\text{inactive}(x) @f$, constraint} */
  [[nodiscard]] const Expression& inactive_soi() const { return inactive_soi_; }
  /**
   * @getter{current Sum of Infeatsibilities expression based on the state, constraint,
   * If the constraint is not fixed yet\, return the expression @f$ 0 @f$}
   */
  [[nodiscard]] const Expression& soi() const;
  /** @getter{state, constraint} */
  [[nodiscard]] PiecewiseConstraintState state() const { return state_; }

 protected:
  const mpq_class* lower_bound_;  ///< Lower bound of the constraint
  const mpq_class* upper_bound_;  ///< Upper bound of the constraint

  const Variable active_var_;  ///< Boolean variable associated with the @f$ y = f_\text{active}(x) @f$ theory literal
  const Variable
      inactive_var_;           ///< Boolean variable associated with the @f$ y = f_\text{inactive}(x) @f$ theory literal
  const Variable theory_var_;  ///< Theory variable @f$ y @f$

  const Expression active_soi_;    ///< Expression @f$ y - f_\text{active}(x) @f$
  const Expression inactive_soi_;  ///< Expression @f$ y - f_\text{inactive}(x) @f$

  PiecewiseConstraintState state_;  ///< State of the constraint
};

std::ostream& operator<<(std::ostream& os, const PiecewiseLinearConstraint& gc);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::PiecewiseLinearConstraint)

#endif
