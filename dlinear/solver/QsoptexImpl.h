/**
 * @file QsoptexImpl.h
 * @author dlinear
 * @date 14 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */

#ifndef DLINEAR5_DLINEAR_SOLVER_QSOPTEXIMPL_H_
#define DLINEAR5_DLINEAR_SOLVER_QSOPTEXIMPL_H_

#include "dlinear/solver/ContextImpl.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/logging.h"
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
  optional <Box> CheckSatCore(const ScopedVector<Formula> &stack, Box box, mpq_class *actual_precision);
  int CheckOptCore(const ScopedVector<Formula> &stack, mpq_class *obj_lo, mpq_class *obj_up, Box *box);

  void MinimizeCore(const Expression &obj_expr);

  QsoptexSatSolver sat_solver_; // TODO: QsoptexSatSolver sat_solver_;
  QsoptexTheorySolver theory_solver_; // TODO: QsoptexTheorySolver theory_solver_;
  Expression obj_expr_;
};

} // dlinear

#endif //DLINEAR5_DLINEAR_SOLVER_QSOPTEXIMPL_H_
