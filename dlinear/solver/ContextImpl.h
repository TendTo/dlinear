/**
 * @file ContextImpl.h
 * @author dlinear
 * @date 14 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */
#pragma once

#include <memory>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "dlinear/solver/Context.h"
#include "dlinear/solver/LpResult.h"
#include "dlinear/solver/SatSolver.h"
#include "dlinear/solver/TheorySolver.h"
#include "dlinear/util/ScopedVector.hpp"

namespace dlinear {

class Context::Impl {
 public:
  Impl();
  explicit Impl(const Config &config);
  explicit Impl(Config &&config);
  Impl(const Impl &) = delete;
  Impl(Impl &&) = delete;
  Impl &operator=(const Impl &) = delete;
  Impl &operator=(Impl &&) = delete;
  virtual ~Impl() = default;

  virtual void Assert(const Formula &f);
  virtual void Pop();
  virtual void Push();

  SatResult CheckSat(mpq_class *precision);
  LpResult CheckOpt(mpq_class *obj_lo, mpq_class *obj_up);
  void DeclareVariable(const Variable &v, bool is_model_variable);
  void SetDomain(const Variable &v, const Expression &lb, const Expression &ub);
  void Minimize(const std::vector<Expression> &functions);
  void Maximize(const std::vector<Expression> &functions);
  void SetInfo(const std::string &key, double val);
  void SetInfo(const std::string &key, const std::string &val);
  [[nodiscard]] std::string GetInfo(const std::string &key) const;
  void SetInterval(const Variable &v, const mpq_class &lb, const mpq_class &ub);
  void SetLogic(const Logic &logic);
  void SetOption(const std::string &key, double val);
  void SetOption(const std::string &key, const std::string &val);
  [[nodiscard]] std::string GetOption(const std::string &key) const;
  const Config &config() const { return config_; }
  Config &mutable_config() { return config_; }
  const ScopedVector<Formula> &assertions() const;
  Box &box() { return boxes_.last(); }
  const Box &get_model() { return model_; }
  bool have_objective() const;
  bool is_max() const;

 private:
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

  /** Return the current box in the stack. */
  virtual SatResult CheckSatCore(mpq_class *actual_precision);
  virtual LpResult CheckOptCore(mpq_class *obj_lo, mpq_class *obj_up);

  virtual void MinimizeCore(const Expression &obj_expr);

  /** Mark the variable @p v as a model variable. */
  void MarkModelVariable(const Variable &v);

  /** Check if the variable @p v is a model variable or not. */
  bool IsModelVariable(const Variable &v) const;

  /**
   * Extract a model from the @p box. Note that @p box might include
   * non-model variables (i.e. variables introduced by if-then-else
   * elimination). This function creates a new box which is free of
   * those non-model variables.
   *
   * @param box box to extract a model from.
   * @return box which is free of non-model variables.
   */
  Box ExtractModel(const Box &box) const;

  Config config_;
  std::optional<Logic> logic_{};
  std::unordered_map<std::string, std::string> info_;
  std::unordered_map<std::string, std::string> option_;

  ScopedVector<Box> boxes_;                           ///< Stack of boxes. The top one is the current box.
  ScopedVector<Formula> stack_;                       ///< Stack of asserted formulas.
  std::unordered_set<Variable::Id> model_variables_;  ///< Set of model variables.

  Box model_;  ///< Stores the result of the latest checksat. If the checksat result was UNSAT, the model is empty.

  bool have_objective_;  ///< Keeps track of whether or not there is an objective function.
  bool is_max_;          ///< Keeps track of whether or not the objective function is being maximized.
  bool theory_loaded_;   ///< Whether the theory solver has been loaded with all the assertions parsed by the SAT

  PredicateAbstractor predicate_abstractor_;  ///< Converts the theory literals to boolean variables.
  // TODO: these could become templated classes for added efficiency
  std::unique_ptr<SatSolver> sat_solver_;        ///< SAT solver.
  std::unique_ptr<TheorySolver> theory_solver_;  ///< Theory solver.
};

}  // namespace dlinear
