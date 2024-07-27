/**
 * @file ContextImpl.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Implementation of Context.
 *
 * The context juggles between the SAT solver and the theory solver, in order to produce a model.
 * Using a forward declaration of ContextImpl in Context.h, we can avoid including this file in Context.h.
 * This structure is based on the pimpl idiom (https://en.cppreference.com/w/cpp/language/pimpl).
 */
#pragma once

#include <memory>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#ifndef NDEBUG
#include <set>
#endif

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/Context.h"
#include "dlinear/solver/Logic.h"
#include "dlinear/solver/LpResult.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/solver/SatSolver.h"
#include "dlinear/solver/SmtSolverOutput.h"
#include "dlinear/solver/TheorySolver.h"
#include "dlinear/symbolic/IfThenElseEliminator.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/ScopedVector.hpp"

namespace dlinear {

/**
 * The context juggles between the SAT solver and the theory solver, in order to produce a model.
 * Using a forward declaration of ContextImpl in Context.h, we can avoid including this file in Context.h.
 * This structure is based on the pimpl idiom (https://en.cppreference.com/w/cpp/language/pimpl).
 */
class Context::Impl {
 public:
  /**
   * Construct a context with @p config.
   * @param config the configuration of the context
   */
  explicit Impl(Config &config, SmtSolverOutput *output = nullptr);
  Impl(const Impl &) = delete;
  Impl(Impl &&) = delete;
  Impl &operator=(const Impl &) = delete;
  Impl &operator=(Impl &&) = delete;

  /**
   * Assert a formula @p f.
   *
   * The new formula is added to the box.
   * @param f the formula to be asserted
   */
  void Assert(const Formula &f);
  /**
   * Assert an ITE expression @p e in order to reuse it later and return the corresponding fresh variable introduced.
   *
   * If @p e is not an ITE expression, it will be returned unchanged.
   * No recursion is performed.
   * @param e ITE expression to be asserted
   * @return fresh variable introduced to represent the ITE expression or simple expression if a simplification happened
   */
  Expression AssertIte(const Expression &e);
  /**
   * Assert a max expression @p e in order to reuse it later and return the corresponding fresh variable introduced.
   *
   * If @p e is not a max expression, it will be returned unchanged.
   * No recursion is performed.
   * @param e max expression to be asserted
   * @return fresh variable introduced to represent the max expression or simple expression if a simplification happened
   */
  Expression AssertMax(const Expression &e);

  /** Pop the top of the stack of assertions. */
  void Pop();
  /** Push the current set of assertions to the stack. */
  void Push();
  /**
   * Check the satisfiability of the asserted formulas, and sets
   * @p actual_precision to the actual max infeasibility where appropriate.
   * @param[in,out] actual_precision initialized with the desired precision, it will be
   * set to the lowest possible precision below the given one that satisfies the
   * constraints.
   * @return the satisfiability result.
   */
  SatResult CheckSat(mpq_class *precision);
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
  void DeclareVariable(const Variable &v, bool is_model_variable);
  /**
   * Set a domain for the variable @p v, restricting it to the interval @f$ [lb, ub] @f$.
   * @param v the variable to be declared
   * @param lb the lower bound of the variable
   * @param ub the upper bound of the variable
   */
  void SetDomain(const Variable &v, const Expression &lb, const Expression &ub);
  /**
   * Assert a formula minimizing a cost function @p f.
   * @param f the cost function to be minimized
   */
  void Minimize(const Expression &obj_function);
  /**
   * Assert a formula maximizing a cost function @p f.
   * @param f the cost function to be maximized
   */
  void Maximize(const Expression &obj_function);
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
  /**
   * Get the configuration of the context.
   * @return configuration of the context
   */
  const Config &config() const { return config_; }
  /**
   * Get the the asserted formulas.
   * @note that the returned vector can be a proper subset of the asserted formulas.
   * For example, when `x <= 5` is asserted, box() is updated to have this information and the formula is thrown away.
   */
  const ScopedVector<Formula> &assertions() const;
  /**
   * Get the current active box from the top of the @ref stack_ of boxes.
   * @return the active box of the context
   */
  Box &box() { return boxes_.last(); }
  /**
   * Get a representation of a model computed by the solver in response to the last invocation of the check-sat.
   * @return the model computed by the solver
   */
  const Box &get_model() { return model_; }

  [[nodiscard]] const SmtSolverOutput *solver_output() const { return output_; }
  SmtSolverOutput *m_solver_output() { return output_; }
  /**
   * Check whether or not there is an objective function (which may be zero) to optimize.
   * @return true if there is an objective function to optimize. @ref CheckOpt() will be called
   * @return false if there is no objective function. @ref CheckSat() will be called
   */
  bool have_objective() const;
  /**
   * Check whether or not the objective function (if present) is a maximization.
   * @return true if the original objective function is a maximization
   * @return false if the original objective function is a minimization
   */
  bool is_max() const;

 private:
  static const Config default_config_;  ///< Default configuration of the context if none is provided.

  /**
   * Get the correct theory solver subclass based on the configuration.
   * @param config configuration of the context determining the theory solver to use
   * @return theory solver subclass
   */
  std::unique_ptr<TheorySolver> GetTheorySolver(const Config &config);

  /**
   * Add the variable @p v to the current box. This is used to
   * introduce a non-model variable to solver. For a model variable,
   * `DeclareVariable` should be used. But `DeclareVariable` should be
   * called from outside of this class. Any methods in this class
   * should not call it directly.
   *
   * @param v The variable to be added to the current box.
   */
  void AddToBox(const Variable &v);

  /**
   * The TheorySolver found a conflict and the explanation is the set of literals that are responsible.
   *
   * The explanation is returned to the SAT solver so that it can use it to learn a new clause and backtrack,
   * looking for a new, non-conflicting assignment.
   * @param explanation set of literals that are responsible for the conflict
   */
  void LearnExplanation(const LiteralSet &explanation);
  /**
   * The TheorySolver found a number of conflicts and the explanations are the set of literals that are responsible.
   *
   * The explanations are returned to the SAT solver so that it can use them to learn a new clause and backtrack,
   * looking for a new, non-conflicting assignment.
   * @param explanations set of sets of literals that are responsible for the conflict
   */
  void LearnExplanations(const TheorySolver::Explanations &explanations);

  /**
   * Check the satisfiability of the current set of assertions.
   *
   * This method is called internally by @ref CheckSat().
   * @param[out] actual_precision the actual precision of the model
   * @return the result of the check-sat
   * @see CheckSat
   */
  SatResult CheckSatCore(mpq_class *actual_precision);
  /**
   * Check the satisfiability of the asserted formulas, and (where possible) optimizes an objective function over them.
   *
   * This method is called internally by @ref CheckOpt().
   * @param[out] obj_lo objective function lower bound
   * @param[out] obj_up objective function upper bound
   * @return the result of the check-opt
   * @see CheckOpt
   */
  LpResult CheckOptCore(mpq_class *obj_lo, mpq_class *obj_up);

  void MinimizeCore(const Expression &obj_expr);

  /**
   * Mark the variable @p v as a model variable.
   * @param v the variable to be marked as a model variable
   */
  void MarkModelVariable(const Variable &v);

  /**
   * Check if the variable @p v is a model variable.
   * @param v the variable to be checked
   * @return true if the variable is a model variable
   * @return false if the variable is not a model variable
   */
  bool IsModelVariable(const Variable &v) const;

  /**
   * Extract a model from the @p box.
   *
   * Note that @p box might include non-model variables (i.e. variables introduced by if-then-else elimination).
   * This function creates a new box which is free of those non-model variables.
   * @param box box to extract a model from.
   * @return box which is free of non-model variables.
   */
  Box ExtractModel(const Box &box) const;

  /**
   * Update the @ref output_ with the last @p smt_result .
   *
   * Depending on the configuration, the model could be stored in the output, assertion and statistics could be updated.
   * Finally, the result will be printed to the standard output, if the configuration allows it.
   * @warning Precision and bounds are not updated.
   * @param smt_result smt result to present the user
   */
  void UpdateAndPrintOutput(SmtResult smt_result) const;

  Config &config_;                 ///< Configuration of the context. It could be modified by the problem instance.
  SmtSolverOutput *const output_;  ///< Output of the SMT solver. Stores the result of the checksat and some statistics.

  std::optional<Logic> logic_;  ///< SMT Logic of the context. Must be among the supported logics.
  std::unordered_map<std::string, std::string> info_;    ///< Key-value pairs of information.
  std::unordered_map<std::string, std::string> option_;  ///< Key-value pairs of options.

  ScopedVector<Box> boxes_;                           ///< Stack of boxes. The top one is the current box.
  ScopedVector<Formula> stack_;                       ///< Stack of asserted formulas.
  std::unordered_set<Variable::Id> model_variables_;  ///< Set of model variables.

  Box model_;  ///< Stores the result of the latest checksat. If the checksat result was UNSAT, the model is empty.

  bool have_objective_;  ///< Keeps track of whether or not there is an objective function.
  bool is_max_;          ///< Keeps track of whether or not the objective function is being maximized.
  bool theory_loaded_;   ///< Whether the theory solver has been loaded with all the assertions parsed by the SAT

  PredicateAbstractor predicate_abstractor_;  ///< Converts the theory literals to boolean variables.
  IfThenElseEliminator ite_eliminator_;       ///< Eliminates if-then-else expressions from the formula.
  // TODO: these could become templated classes for added efficiency
  const std::unique_ptr<SatSolver> sat_solver_;        ///< SAT solver.
  const std::unique_ptr<TheorySolver> theory_solver_;  ///< Theory solver.

#ifndef NDEBUG
  std::set<LiteralSet> explanations_so_far;  ///< Set of explanations that have been learned so far.
#endif
};

}  // namespace dlinear
