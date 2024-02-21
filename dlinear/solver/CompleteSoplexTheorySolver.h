/**
 * @file CompleteSoplexTheorySolver.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Complete version of SoplexTheorySolver.
 *
 * The LP solver used is Soplex.
 * This solver is complete. It means that it will always solve the linear problem exactly.
 */
#pragma once

#ifndef DLINEAR_ENABLED_SOPLEX
#error SoPlex is not enabled. Please enable it by adding "--//tools:enable_soplex" to the bazel command.
#endif

#include <optional>

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/SoplexTheorySolver.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"

namespace dlinear {

class CompleteSoplexTheorySolver : public SoplexTheorySolver {
 public:
  explicit CompleteSoplexTheorySolver(PredicateAbstractor& predicate_abstractor, const Config& config = Config{});

  std::optional<LiteralSet> EnableLiteral(const Literal& lit) override;

  void AddVariable(const Variable& var) override;

  void AddLiteral(const Literal& lit) override;

  SatResult CheckSat(const Box& box, mpq_class* actual_precision, LiteralSet& explanation) override;

  void Reset(const Box& box) override;

 protected:
  bool SetSPXVarBound(const Bound& bound, int spx_col) override;

  std::vector<std::set<soplex::Rational>> spx_diff_;
};

}  // namespace dlinear
