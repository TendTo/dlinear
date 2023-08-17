/**
 * @file Context.h
 * @author dlinear
 * @date 13 Aug 2023
 * @copyright 2023 dlinear
 * @brief Context holding the information about the resolution of the problem.
 *
 * While the solver is running, the context holds the information about the
 * problem being solved. It also holds the information about the
 * program version.
 */

#ifndef DLINEAR5_DLINEAR_UTIL_CONTEXT_H_
#define DLINEAR5_DLINEAR_UTIL_CONTEXT_H_

#include <iostream>
#include <memory>

#include <tl/optional.hpp>

#include "dlinear/version.h"
#include "dlinear/libs/gmp.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"
#include "dlinear/smt2/logic.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/ScopedVector.hpp"

namespace dlinear {

enum {
  SAT_NO_RESULT = 0,
  SAT_UNSOLVED,
  SAT_UNSATISFIABLE,
  SAT_SATISFIABLE,
  SAT_DELTA_SATISFIABLE,
};

enum {
  LP_NO_RESULT = 0,
  LP_UNSOLVED,
  LP_INFEASIBLE,
  LP_UNBOUNDED,
  LP_DELTA_OPTIMAL,
};

/**
 * @brief Context class that holds a set of constraints and provide
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

  /** Destructor (Defaulted in .cc file. Needed here for compilation). */
  ~Context();

  /** Deleted copy-assign. */
  Context &operator=(const Context &) = delete;

  /** Deleted move-assign. */
  Context &operator=(Context &&) = delete;

  /** Constructs a context with @p config. */
  explicit Context(Config config);

  /** Asserts a formula @p f. */
  void Assert(const Formula &f);

  /**
   * Checks the satisfiability of the asserted formulas, and sets
   * @p actual_precision (write-only) to the actual max infeasibility where
   * appropriate.
   */
  tl::optional <Box> CheckSat(mpq_class *actual_precision);

  /**
   * Checks the satisfiability of the asserted formulas, and (where
   * possible) optimizes an objective function over them.
   */
  int CheckOpt(mpq_class *obj_lo, mpq_class *obj_up, Box *model);

  /**
   * Declare a variable @p v. By default @p v is considered as a
   * model variable. If @p is_model_variable is false, it is declared as
   * a non-model variable and will not appear in the model.
   */
  void DeclareVariable(const Variable &v, bool is_model_variable = true);

  /**
   * Declare a variable @p v which is bounded by an interval `[lb,
   * ub]`. By default @p v is considered as a model variable. If @p
   * is_model_variable is false, it is declared as a non-model variable
   * and will not appear in the model.
   */
  void DeclareVariable(const Variable &v, const Expression &lb, const Expression &ub, bool is_model_variable = true);

  /** Closes the context */
  static void Exit();

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

  /** Sets the interval of @p v in the current box (top one in boxes_). */
  void SetInterval(const Variable &v, const mpq_class &lb, const mpq_class &ub);

  /** Sets the current logic to be @p logic. */
  void SetLogic(const Logic &logic);

  /** Sets an option @p key with a value @p val. */
  void SetOption(const std::string &key, double val);

  /** Sets an option @p key with a value @p val */
  void SetOption(const std::string &key, const std::string &val);

  /** Returns a const reference of configuration */
  [[nodiscard]] const Config &config() const;

  /** Returns a mutable reference of configuration */
  Config &mutable_config();

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
  [[nodiscard]] const Box &get_model() const;

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

 private:
  // This header is exposed to external users as a part of API. We use
  // PIMPL idiom to hide internals and to reduce number of '#includes' in this
  // file.
  class Impl;
  class SoplexImpl;
  class QsoptexImpl;

  static std::unique_ptr <Context::Impl> make_impl(const Config &config);

  std::unique_ptr <Impl> impl_;
};

} // dlinear

#endif //DLINEAR5_DLINEAR_UTIL_CONTEXT_H_
