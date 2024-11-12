/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * DeltaLpTheorySolver class.
 */
#pragma once

#include "dlinear/solver/theory_solver/qf_lra/LpTheorySolver.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

class DeltaLpTheorySolver : public LpTheorySolver {
 public:
  explicit DeltaLpTheorySolver(const PredicateAbstractor& predicate_abstractor,
                               const std::string& class_name = "DeltaLpTheorySolver");

  void AddLiteral(const Variable& formula_var, const Formula& formula) final;
  bool EnableLiteral(const Literal& lit, const ConflictCallback& conflict_cb) final;

  TheoryResult CheckSatCore(mpq_class* actual_precision, const ConflictCallback& conflict_cb) final;
};

}  // namespace dlinear
