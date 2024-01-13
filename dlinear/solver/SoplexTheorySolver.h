//
// Created by c3054737 on 12/01/24.
//
#pragma once

#include "dlinear/libs/soplex.h"
#include "dlinear/solver/TheorySolver.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

class SoplexTheorySolver : public TheorySolver {
 public:
  explicit SoplexTheorySolver(const Config& config = Config{});

  void SetSPXVarBound(const Variable& var, char type, const mpq_class& value);

  void AddTheoryVariable(const Variable& var) override;

  void EnableTheoryLiteral(const Literal& lit, const VarToTheoryLiteralMap& var_to_theory_literals) override;

  SatResult CheckSat(const Box& box, mpq_class* actual_precision) override;

 private:
  void ResetLinearProblem(const Box& box) override;

  // Exact LP solver (SoPlex)
  soplex::SoPlex spx_;
  soplex::VectorRational spx_lower_;
  soplex::VectorRational spx_upper_;

  std::vector<mpq_class> spx_rhs_;
  std::vector<char> spx_sense_;
};

}  // namespace dlinear
