/**
 * @file QsoptexImpl.h
 * @author dlinear
 * @date 14 Aug 2023
 * @copyright 2023 dlinear
 * @brief Context implementation for the Qsoptex LP solver.
 *
 * Long Description
 */
#pragma once

#include <vector>

#include "dlinear/solver/ContextImpl.h"
#include "dlinear/solver/QsoptexSatSolver.h"
#include "dlinear/solver/QsoptexTheorySolver.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

class Context::QsoptexImpl : public Context::Impl {
 public:
  QsoptexImpl();
  explicit QsoptexImpl(Config config);

  void Assert(const Formula &f) override;
  void Pop() override;
  void Push() override;

 protected:
  // Returns the current box in the stack.
  std::optional<Box> CheckSatCore(const ScopedVector<Formula> &stack, Box box, mpq_class *actual_precision) override;
  int CheckOptCore(const ScopedVector<Formula> &stack, mpq_class *obj_lo, mpq_class *obj_up, Box *box) override;

  void MinimizeCore(const Expression &obj_expr) override;

  QsoptexSatSolver sat_solver_;        ///< SAT solver.
  QsoptexTheorySolver theory_solver_;  ///< Theory solver.
  Expression obj_expr_;                ///< Objective expression.
};

}  // namespace dlinear
