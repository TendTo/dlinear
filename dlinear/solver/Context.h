/**
 * @file Context.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Context holding the information about the resolution of the problem.
 *
 * While the solver is running, the context holds the information about the
 * problem being solved. It also holds the information about the
 * program version.
 */
#pragma once

#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/Logic.h"
#include "dlinear/solver/LpResult.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/ScopedVector.hpp"
#include "dlinear/util/Stats.h"

namespace dlinear {

/**
 * Context class that holds a set of constraints and provide
 * Assert/Push/Pop/CheckSat functionalities.
 *
 * @note The implementation details are in context_impl.h file.
 */
class Context {
 public:
  /** Constructs a context with an empty configuration. */
  Context();

  /** Deleted copy constructor. */
  Context(const Context &context) = delete;

  /** Move constructor. */
  Context(Context &&context) noexcept;

  /** Destructor (Defaulted in source file. Needed here for compilation). */
  ~Context();

  /** Deleted copy-assign. */
  Context &operator=(const Context &) = delete;

  /** Deleted move-assign. */
  Context &operator=(Context &&) = delete;

  /** Constructs a context with @p config. */
  explicit Context(const Config &config);

  /**
   * Asserts a formula @p f.
   * The new formula is added to the box.
   *
   * @param f the formula to be asserted
   */
  void Assert(const Formula &f);

  /**
   * Checks the satisfiability of the asserted formulas, and sets
   * @p actual_precision to the actual max infeasibility where
   * appropriate.
   *
   * @param[in,out] actual_precision initialized with the desired precision, it will be
   * set to the lowest possible precision below the given one that satisfies the
   * constraints.
   * @return the satisfiability result.
   */
  SatResult CheckSat(mpq_class *actual_precision);

  /**
   * Checks the satisfiability of the asserted formulas, and (where
   * possible) optimizes an objective function over them.
   */
  LpResult CheckOpt(mpq_class *obj_lo, mpq_class *obj_up);

  /**
   * Declare a variable @p v. By default @p v is considered as a
   * model variable. If @p IsModelVariable is false, it is declared as
   * a non-model variable and will not appear in the model.
   *
   * @param v the variable to be declared
   * @param is_model_variable whether or not the variable is a model variable
   */
  void DeclareVariable(const Variable &v, bool is_model_variable = true);

  /**
   * Declare a variable @p v which is bounded by an interval `[lb,
   * ub]`. By default @p v is considered as a model variable. If @p
   * IsModelVariable is false, it is declared as a non-model variable
   * and will not appear in the model.
   *
   * @param v the variable to be declared
   * @param lb the lower bound of the variable
   * @param ub the upper bound of the variable
   * @param is_model_variable whether or not the variable is a model variable
   */
  void DeclareVariable(const Variable &v, const Expression &lb, const Expression &ub, bool is_model_variable = true);

  void Exit();

  /** Asserts a formula minimizing a cost function @p f */
  void Minimize(const Expression &f);

  /**
   * Asserts a formula encoding Pareto optimality with a given set of
   * objective functions.
   */
  void Minimize(const std::vector<Expression> &functions);

  /** Asserts a formula maximizing a cost function @p f. */
  void Maximize(const Expression &f);

  /** Pops @p n stacks. */
  void Pop(int n);

  /** Pushes @p n stacks. */
  void Push(int n);

  /** Sets an info @p key with a value @p val. */
  void SetInfo(const std::string &key, double val);

  /** Sets an info @p key with a value @p val. */
  void SetInfo(const std::string &key, const std::string &val);

  [[nodiscard]] std::string GetInfo(const std::string &key) const;

  /** Sets the interval of @p v in the current box (top one in boxes_). */
  void SetInterval(const Variable &v, const mpq_class &lb, const mpq_class &ub);

  /** Sets the current logic to be @p logic. */
  void SetLogic(const Logic &logic);

  /** Sets an option @p key with a value @p val. */
  void SetOption(const std::string &key, double val);

  /** Sets an option @p key with a value @p val */
  void SetOption(const std::string &key, const std::string &val);

  [[nodiscard]] std::string GetOption(const std::string &key) const;

  /** Returns a const reference of configuration */
  [[nodiscard]] const Config &config() const;

  /** Returns a mutable reference of configuration */
  Config &m_config();

  /** Returns the version string */
  static std::string version();

  /** Returns the repository status string */
  static std::string repository_status();

  /**
   * Returns the const reference to the asserted formulas.
   *
   * @note that the returned vector can be a proper subset of the
   * asserted formulas. For example, when `x <= 5` is asserted, box()
   * is updated to have this information (x <= 5) and this formula is
   * thrown away.
   */
  [[nodiscard]] const ScopedVector<Formula> &assertions() const;

  /** Returns the const reference to the top box */
  [[nodiscard]] const Box &box() const;

  /**
   * Returns a representation of a model computed by the solver in
   * response to an invocation of the check-sat.
   */
  [[nodiscard]] const Box &model() const;

  /**
   * Returns whether or not there is an objective function (which may be
   * zero). If true, then CheckOpt() must be used, and not CheckSat(). If
   * false, then CheckSat() must be used, and not CheckOpt().
   */
  [[nodiscard]] bool have_objective() const;

  /**
   * Returns whether or not the objective function (if present) is a
   * maximization. If true, the original objective function has been negated
   * to form a minimization problem.
   */
  [[nodiscard]] bool is_max() const;

  /**
   * Returns the statistics up to the last call to CheckSat of the SAT solver.
   * @return statistics of the SAT solver
   */
  [[nodiscard]] const IterationStats &sat_stats() const;
  /**
   * Returns the statistics up to the last call to CheckSat or CheckOpt of the LP solver.
   * @return statistics of the LP solver
   */
  [[nodiscard]] const IterationStats &theory_stats() const;
  /**
   * Returns the statistics up to the last call to CheckSat or CheckOpt of the formula visitors used by the SAT solver.
   * @return statistics of the predicate abstractor and the CNFizer
   */
  [[nodiscard]] std::tuple<const IterationStats &, const IterationStats &, const IterationStats &>
  formula_visitors_stats() const;

 private:
  // This header is exposed to external users as a part of API. We use
  // PIMPL idiom to hide internals and to reduce number of '#includes' in this
  // file.
  class Impl;

  std::unique_ptr<Impl> impl_;
};

}  // namespace dlinear
