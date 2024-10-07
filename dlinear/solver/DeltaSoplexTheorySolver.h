/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * DeltaSoplexTheorySolver class.
 */
#pragma once

#include <string>

#ifndef DLINEAR_ENABLED_SOPLEX
#error SoPlex is not enabled. Please enable it by adding "--//tools:enable_soplex" to the bazel command.
#endif

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/solver/SoplexTheorySolver.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/Box.h"

namespace dlinear {

/**
 * Delta complete solver using SoPlex.
 *
 * The LP problem is solver exactly, within a given precision, delta.
 * Since the value of delta is considered strictly positive, strict inequalities will be relaxed
 * and not-equal-to constraints ignored.
 */
class DeltaSoplexTheorySolver : public SoplexTheorySolver {
 public:
  explicit DeltaSoplexTheorySolver(PredicateAbstractor& predicate_abstractor,
                                   const std::string& class_name = "DeltaSoplexTheorySolver");

  Explanations EnableLiteral(const Literal& lit) override;

  void AddLiteral(const Variable& formula_var, const Formula& formula) override;

  SatResult CheckSatCore(mpq_class* actual_precision, Explanations& explanations) override;

 private:
  void EnableSpxRow(int spx_row, bool truth) override;
};

}  // namespace dlinear
