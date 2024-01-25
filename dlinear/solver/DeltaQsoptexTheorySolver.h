/**
 * @file DeltaQsoptexTheorySolver.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Delta complete version of QsoptexTheorySolver.
 *
 * The LP solver used is Qsoptex.
 * This solver is delta complete. It means that it will always solve the delta-weakened linear problem,
 * with a positive delta.
 * This translates to a faster approach, for strict inequalities can be immediately discarded or relaxed.
 */
#pragma once

#ifndef DLINEAR_ENABLED_QSOPTEX
#error "QSopt_ex is not enabled. Please enable it by adding \"--\/\/tools:enable_qsoptex\" to the bazel command."
#endif

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/QsoptexTheorySolver.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"

namespace dlinear {

class DeltaQsoptexTheorySolver : public QsoptexTheorySolver {
 public:
  explicit DeltaQsoptexTheorySolver(PredicateAbstractor& predicate_abstractor, const Config& config = Config{});

  std::optional<LiteralSet> EnableLiteral(const Literal& lit) override;

  void AddLiteral(const Literal& lit) override;

  SatResult CheckSat(const Box& box, mpq_class* actual_precision, LiteralSet& explanation) override;
};

}  // namespace dlinear
