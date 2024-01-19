//
// Created by c3054737 on 12/01/24.
//
#pragma once

#include <vector>

#include "dlinear/libs/soplex.h"
#include "dlinear/solver/TheorySolver.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"

namespace dlinear {

class SoplexTheorySolver : public TheorySolver {
 public:
  explicit SoplexTheorySolver(PredicateAbstractor& predicate_abstractor, const Config& config = Config{});

  void AddVariable(const Variable& var) override;

  void Reset(const Box& box) override;

 protected:
  static soplex::Rational infinity_;
  static soplex::Rational ninfinity_;

  bool CheckBounds() override;

  void SetSPXVarBound(const Variable& var, char type, const mpq_class& value);
  void SetSPXVarCoeff(soplex::DSVectorRational& coeffs, const Variable& var, const mpq_class& value);
  void CreateArtificials(int spx_row);

  // Exact LP solver (SoPlex)
  soplex::SoPlex spx_;
  soplex::VectorRational spx_lower_;
  soplex::VectorRational spx_upper_;

  std::vector<mpq_class> spx_rhs_;
  std::vector<char> spx_sense_;
};

}  // namespace dlinear
