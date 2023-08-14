/**
 * @file ContextImpl.h
 * @author dlinear
 * @date 14 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */

#ifndef DLINEAR5_DLINEAR_SOLVER_CONTEXTIMPL_H_
#define DLINEAR5_DLINEAR_SOLVER_CONTEXTIMPL_H_

#include "dlinear/solver/Context.h"
#include "dlinear/util/ScopedVector.hpp"
#include "dlinear/util/logging.h"

#include <unordered_set>

using std::unordered_set;
using std::string;
using std::vector;

namespace dlinear {

class Context::Impl {
 public:
  Impl();
  explicit Impl(Config config);
  Impl(const Impl &) = delete;
  Impl(Impl &&) = delete;
  Impl &operator=(const Impl &) = delete;
  Impl &operator=(Impl &&) = delete;
  virtual ~Impl() = default;

  virtual void Assert(const Formula &f) = 0;
  virtual void Pop() = 0;
  virtual void Push() = 0;

  optional <Box> CheckSat(mpq_class *actual_precision);
  int CheckOpt(mpq_class *obj_lo, mpq_class *obj_up, Box *model);
  void DeclareVariable(const Variable &v, bool is_model_variable);
  void SetDomain(const Variable &v, const Expression &lb, const Expression &ub);
  void Minimize(const vector<Expression> &functions);
  void Maximize(const vector<Expression> &functions);
  void SetInfo(const string &key, double val);
  void SetInfo(const string &key, const string &val);
  void SetInterval(const Variable &v, const mpq_class &lb, const mpq_class &ub);
  void SetLogic(const Logic &logic);
  void SetOption(const string &key, double val);
  void SetOption(const string &key, const string &val);
  const Config &config() const { return config_; }
  Config &mutable_config() { return config_; }
  const ScopedVector<Formula> &assertions() const;
  Box &box() { return boxes_.last(); }
  const Box &get_model() { return model_; }
  bool have_objective() const;
  bool is_max() const;

 protected:
  /**
   * Add the variable @p v to the current box. This is used to
   * introduce a non-model variable to solver. For a model variable,
   * `DeclareVariable` should be used. But `DeclareVariable` should be
   * called from outside of this class. Any methods in this class
   * should not call it directly.
   * @param v The variable to be added to the current box.
   */
  void AddToBox(const Variable &v);

  /** Return the current box in the stack. */
  virtual optional <Box> CheckSatCore(const ScopedVector<Formula> &stack, Box box, mpq_class *actual_precision) = 0;
  virtual int CheckOptCore(const ScopedVector<Formula> &stack, mpq_class *obj_lo, mpq_class *obj_up, Box *model) = 0;

  virtual void MinimizeCore(const Expression &obj_expr) = 0;

  /** Mark the variable @p v as a model variable. */
  void mark_model_variable(const Variable &v);

  /** Check if the variable @p v is a model variable or not. */
  bool is_model_variable(const Variable &v) const;

  /**
   * Extract a model from the @p box. Note that @p box might include
   * non-model variables (i.e. variables introduced by if-then-else
   * elimination). This function creates a new box which is free of
   * those non-model variables.
   * @param box box to extract a model from.
   * @return box which is free of non-model variables.
   */
  Box ExtractModel(const Box &box) const;

  Config config_;
  optional <Logic> logic_{};
  unordered_map<string, string> info_;
  unordered_map<string, string> option_;

  ScopedVector<Box> boxes_; ///< Stack of boxes. The top one is the current box.
  ScopedVector<Formula> stack_; ///< Stack of asserted formulas.
  unordered_set<Variable::Id> model_variables_; ///< Set of model variables.

  Box model_; ///< Stores the result of the latest checksat. If the checksat result was UNSAT, this box holds an empty box.

  bool have_objective_; ///< Keeps track of whether or not there is an objective function.
  bool is_max_; ///< Keeps track of whether or not the objective function is being maximized.
};

} // dlinear

#endif //DLINEAR5_DLINEAR_SOLVER_CONTEXTIMPL_H_
