/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * DeltaQsoptexTheorySolver class.
 */
#pragma once

#ifndef DLINEAR_ENABLED_QSOPTEX
#error QSopt_ex is not enabled. Please enable it by adding "--//tools:enable_qsoptex" to the bazel command.
#endif

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/QsoptexTheorySolver.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"

namespace dlinear {

/**
 * Delta complete solver using QSopt_ex.
 *
 * The LP problem is solver exactly, within a given precision, delta.
 * Since the value of delta is considered strictly positive, strict inequalities will be relaxed
 * and not-equal-to constraints ignored.
 */
class DeltaQsoptexTheorySolver : public QsoptexTheorySolver {
 public:
  explicit DeltaQsoptexTheorySolver(PredicateAbstractor& predicate_abstractor,
                                    const std::string& class_name = "DeltaQsoptexTheorySolver");

  Explanations EnableLiteral(const Literal& lit) override;

  void AddLiteral(const Variable& formula_var, const Formula& formula) override;

  SatResult CheckSatCore(mpq_class* actual_precision, Explanations& explanations) override;

 private:
  void EnableQsxRow(int spx_row, bool truth) override;
};

}  // namespace dlinear
