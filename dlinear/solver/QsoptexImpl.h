/**
 * @file QsoptexImpl.h
 * @author dlinear
 * @date 14 Aug 2023
 * @copyright 2023 dlinear
 * @brief Context implementation for the Qsoptex LP solver.
 *
 * Long Description
 */

#ifndef DLINEAR5_DLINEAR_SOLVER_QSOPTEXIMPL_H_
#define DLINEAR5_DLINEAR_SOLVER_QSOPTEXIMPL_H_

#include "dlinear/solver/ContextImpl.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/logging.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/IfThenElseEliminator.h"
#include "dlinear/solver/QsoptexSatSolver.h"
#include "dlinear/solver/QsoptexTheorySolver.h"

#include <tl/optional.hpp>

namespace dlinear {

class Context::QsoptexImpl : public Context::Impl {
 public:
  QsoptexImpl();
  explicit QsoptexImpl(Config config);

  void Assert(const Formula &f);
  void Pop();
  void Push();

 protected:
  // Returns the current box in the stack.
  tl::optional <Box> CheckSatCore(const ScopedVector<Formula> &stack, Box box, mpq_class *actual_precision);
  int CheckOptCore(const ScopedVector<Formula> &stack, mpq_class *obj_lo, mpq_class *obj_up, Box *box);

  void MinimizeCore(const Expression &obj_expr);

  QsoptexSatSolver sat_solver_; ///< SAT solver.
  QsoptexTheorySolver theory_solver_; ///< Theory solver.
  Expression obj_expr_; ///< Objective expression.
};

} // dlinear

#endif //DLINEAR5_DLINEAR_SOLVER_QSOPTEXIMPL_H_
