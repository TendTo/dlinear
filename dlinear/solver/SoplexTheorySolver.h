/**
 * @file SoplexTheorySolver.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Theory solver using SoPlex.
 *
 * SoPlex is an exact LP solver written in C++.
 * It uses a mixture of techniques, from iterative refinement to precision boosting, in order to efficiently solve LPs
 * exactly.
 */
#pragma once

#ifndef DLINEAR_ENABLED_SOPLEX
#error SoPlex is not enabled. Please enable it by adding "--//tools:enable_soplex" to the bazel command.
#endif

#include <optional>
#include <vector>

#include "dlinear/libs/soplex.h"
#include "dlinear/solver/LpRowSense.h"
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

  void UpdateModelBounds() override;
  void UpdateExplanation(LiteralSet& explanation) override;

  virtual bool SetSPXVarBound(const Bound& bound, int spx_col) = 0;
  /**
   * Parse a row and return the vector of coefficients to apply to the decisional variables.
   *
   * Parse an formula representing a row in order to produce store the rhs term in @link spx_rhs_ @endlink and create a vector
   * of coefficients for the row to pass to the LP solver
   * @param formula symbolic formula representing the row
   * @return vector of coefficients to apply to the decisional variables in the row
   */
  soplex::DSVectorRational ParseRowCoeff(const Formula& formula);
  void SetSPXVarCoeff(soplex::DSVectorRational& coeffs, const Variable& var, const mpq_class& value) const;
  void CreateArtificials(int spx_row);

  // Exact LP solver (SoPlex)
  soplex::SoPlex spx_;
  soplex::VectorRational spx_lower_;
  soplex::VectorRational spx_upper_;

  std::vector<mpq_class> spx_rhs_;
  std::vector<LpRowSense> spx_sense_;
};

}  // namespace dlinear
