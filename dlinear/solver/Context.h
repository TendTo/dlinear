/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Context class.
 */
#pragma once

#include <memory>
#include <string>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/Logic.h"
#include "dlinear/solver/LpResult.h"
#include "dlinear/solver/PiecewiseLinearConstraint.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/solver/SmtSolverOutput.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/ScopedVector.hpp"

namespace dlinear {

/**
 * Context class that holds the set of constraints and provide Assert/Push/Pop/CheckSat functionalities.
 * @note The implementation is hidden in the Context::Impl class.
 */
class Context {
 public:
  /**
   * Construct a context with @p config.
   * If @p smt_solver_output is not null, it will be used to store the output of the SMT solver
   * as well as some statistics.
   * @param config the configuration of the context
   */
  explicit Context(Config &config, SmtSolverOutput * = nullptr);
  Context(const Context &context) = delete;
  Context(Context &&context) noexcept;
  Context &operator=(const Context &) = delete;
  Context &operator=(Context &&) = delete;
  ~Context();

  /**
   * Assert a formula @p f.
   *
   * The new formula is added to the box.
   * @param f the formula to be asserted
   */
  void Assert(const Formula &f);
  /**
   * Assert a piecewise linear function with two possible branches.
   *
   * Consider a piecewise linear function that assigns either @p active or @p inactive to @p var depending on @p cond
   * @f[
   * \text{var} =\begin{cases}
   * \text{active} & \text{if } cond \newline
   * \text{inactive} & \text{otherwise}
   * \end{cases}
   * @f]
   * Assigning @f$ \mathcal{A} = (\text{active} = \text{var}) @f$ and
   * @f$ \mathcal{B} = (\text{var} = \text{inactive}) @f$, we introduce the following assertions:
   * @f[
   * (\mathcal{A} \lor \neg cond) \land (\mathcal{B} \lor cond) \land (cond \lor \neg cond)
   * @f]
   * Note that the last clause is a tautology, but it forces the sat solver to assign a boolean value to cond and
   * hopefully skip either @f$ \mathcal{A} @f$ or @f$ \mathcal{B} @f$.
   * @param var the variable to be assigned
   * @param cond the condition to be checked
   * @param active the value of the variable if the condition is true
   * @param inactive the value of the variable if the condition is false
   */
  void AssertPiecewiseLinearFunction(const Variable &var, const Formula &cond, const Expression &active,
                                     const Expression &inactive);

  /**
   * Check the satisfiability of the asserted formulas, and sets
   * @p actual_precision to the actual max infeasibility where appropriate.
   * @param[out] actual_precision initialized with the desired precision, it will be
   * set to the lowest possible precision below the given one that satisfies the
   * constraints.
   * @return the satisfiability result.
   */
  SatResult CheckSat(mpq_class *actual_precision);
  /**
   * Check the satisfiability of the asserted formulas, and (where possible) optimizes an objective function over them.
   *
   * If a solution is found, the @p obj_lo and @p obj_up store the lower and upper bounds of the objective function.
   * @param[out] obj_lo the lower bound of the objective function
   * @param[out] obj_up the upper bound of the objective function
   */
  LpResult CheckOpt(mpq_class *obj_lo, mpq_class *obj_up);

  /**
   * Declare a variable @p v.
   *
   * By default @p v is considered as a model variable.
   * If @p IsModelVariable is false, it is declared as a non-model variable and will not appear in the model.
   * @param v the variable to be declared
   * @param is_model_variable whether or not the variable is a model variable
   */
  void DeclareVariable(const Variable &v, bool is_model_variable = true);
  /**
   * Declare a variable @p v which is bounded by an interval @f$ [lb, ub] @f$.
   *
   * By default @p v is considered as a model variable.
   * If @p is_model_variable is false, it is declared as a non-model variable and will not appear in the model.
   * @param v the variable to be declared
   * @param lb the lower bound of the variable
   * @param ub the upper bound of the variable
   * @param is_model_variable whether or not the variable is a model variable
   */
  void DeclareVariable(const Variable &v, const Expression &lb, const Expression &ub, bool is_model_variable = true);

  const PiecewiseLinearConstraint &AddGuidedConstraint(std::unique_ptr<PiecewiseLinearConstraint> &&constraint);

  /**
   * Exit the context.
   *
   * Does nothing but prints a debug message.
   */
  void Exit();

  /**
   * Assert a formula minimizing a cost function @p f.
   * @param f the cost function to be minimized
   */
  void Minimize(const Expression &f);

  /**
   * Assert a formula maximizing a cost function @p f.
   * @param f the cost function to be maximized
   */
  void Maximize(const Expression &f);

  /**
   * Pop @p n stacks.
   * @param n the number of stacks to be popped
   */
  void Pop(int n);
  /**
   * Push @p n stacks.
   * @param n number of stacks to be pushed
   */
  void Push(int n);
  /**
   * Set an info @p key with a value @p val.
   * @param key the key of the info
   * @param val the value of the info
   */
  void SetInfo(const std::string &key, const std::string &val);
  /**
   * Get the info @p key.
   * @param key the key of the info
   * @return value of the info
   */
  [[nodiscard]] std::string GetInfo(const std::string &key) const;
  /**
   * Set the interval of @p v to @f$ [lb, ub] @f$ in the current box (top one in boxes_).
   * @param v the variable to be set
   * @param lb the lower bound of the variable
   * @param ub the upper bound of the variable
   */
  void SetInterval(const Variable &v, const mpq_class &lb, const mpq_class &ub);
  /**
   * Set the current logic to @p logic.
   * @param logic the logic to be set
   */
  void SetLogic(Logic logic);
  /**
   * Set an option @p key with a value @p val.
   * @param key the key of the option
   * @param val the value of the option
   */
  void SetOption(const std::string &key, const std::string &val);
  /**
   * Get the option @p key.
   * @param key the key of the option
   * @return value of the option
   */
  [[nodiscard]] std::string GetOption(const std::string &key) const;

  /** @getter{configuration, context}*/
  [[nodiscard]] const Config &config() const;
  /**
   * Get the the asserted formulas.
   * @note that the returned vector can be a proper subset of the asserted formulas.
   * For example, when `x <= 5` is asserted, box() is updated to have this information and the formula is thrown away.
   */
  [[nodiscard]] const ScopedVector<Formula> &assertions() const;
  /**
   * Get the current active box from the top of the stack of boxes.
   * @return the active box of the context
   */
  [[nodiscard]] const Box &box() const;
  /**
   * Get a representation of a model computed by the solver in response to the last invocation of the check-sat.
   * @return the model computed by the solver
   */
  [[nodiscard]] const Box &model() const;
  /**
   * Check whether or not there is an objective function (which may be zero) to optimize.
   * @return true if there is an objective function to optimize. @ref CheckOpt() will be called
   * @return false if there is no objective function. @ref CheckSat() will be called
   */
  [[nodiscard]] bool have_objective() const;
  [[nodiscard]] const SmtSolverOutput *solver_output() const;
  SmtSolverOutput *m_solver_output();
  /** @getter{predicate_abstractor, context}*/
  const PredicateAbstractor &predicate_abstractor() const;

  /**
   * Check whether or not the objective function (if present) is a maximization.
   * @return true if the original objective function is a maximization
   * @return false if the original objective function is a minimization
   */
  [[nodiscard]] bool is_max() const;

  /**
   * Check whether the @p model satisfies all the assertions loaded in the context.
   *
   * In other words, verifies if it is a SAT assignment for the input variables.
   * @param model assignment to check
   * @return true if the @p model satisfies all assignments
   * @return false if there is at leas an assignment not satisfied by the @p model
   */
  [[nodiscard]] bool Verify(const Box &model) const;

 private:
  /**
   * This header is exposed to external users as a part of API.
   * We use PIMPL idiom to hide internals and to reduce number of '#includes' in this file.
   */
  class Impl;

  std::unique_ptr<Impl> impl_;  ///< Pointer to the implementation of the context
};

}  // namespace dlinear
