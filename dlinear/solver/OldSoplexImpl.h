/**
 * @file SoplexImpl.h
 * @author dlinear
 * @date 25 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */
#pragma once

#include <optional>
#include <utility>
#include <vector>

#include "dlinear/solver/ContextImpl.h"
#include "dlinear/solver/OldSoplexSatSolver.h"
#include "dlinear/solver/OldSoplexTheorySolver.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

// The actual implementation.
class Context::SoplexImpl : public Context::Impl {
 public:
  SoplexImpl();
  explicit SoplexImpl(const Config &config);

  void Assert(const Formula &f) override;
  void Pop() override;
  void Push() override;

 protected:
  // Returns the current box in the stack.
  SatResult CheckSatCore(const ScopedVector<Formula> &stack, Box *model, mpq_class *actual_precision) override;
  int CheckOptCore(const ScopedVector<Formula> &stack, mpq_class *obj_lo, mpq_class *obj_up, Box *model) override;

  void MinimizeCore(const Expression &obj_expr) override;

  SoplexSatSolver sat_solver_;
  SoplexTheorySolver theory_solver_;
};

}  // namespace dlinear
