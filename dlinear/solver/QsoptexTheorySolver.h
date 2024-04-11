/**
 * @file QsoptexTheorySolver.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence GPL-3.0 license
 * @brief Theory solver using QSopt_ex.
 *
 * QSopt_ex is an exact LP solver written in C.
 * It uses the technique of precision boosting to efficiently solve LPs exactly.
 */
#pragma once

#ifndef DLINEAR_ENABLED_QSOPTEX
#error QSopt_ex is not enabled. Please enable it by adding "--//tools:enable_qsoptex" to the bazel command.
#endif

#include <vector>

#include "dlinear/libs/libqsopt_ex.h"
#include "dlinear/solver/LpRowSense.h"
#include "dlinear/solver/TheorySolver.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"

namespace dlinear {

extern "C" void QsoptexCheckSatPartialSolution(mpq_QSdata const *prob, mpq_t *x, const mpq_t infeas, const mpq_t delta,
                                               void *data);

class QsoptexTheorySolver : public TheorySolver {
 public:
  QsoptexTheorySolver(PredicateAbstractor &predicate_abstractor, const std::string &class_name = "QsoptexTheorySolver");
  ~QsoptexTheorySolver() override;

  void AddVariable(const Variable &var) override;
  void Reset(const Box &box) override;

 protected:
  void SetLinearObjective(const Expression &expr);
  void ClearLinearObjective();

  void UpdateModelBounds() override;
  void UpdateExplanation(LiteralSet &explanation) override;

  void SetQPXVarBound();
  void SetQSXVarCoef(int qsx_row, const Variable &var, const mpq_class &value);
  void SetQSXVarObjCoef(const Variable &var, const mpq_class &value);
  bool SetQSXVarBound(const Bound &bound, int qsx_col);

  bool continuous_output_;
  bool with_timings_;

  // Exact LP solver (QSopt_ex)
  mpq_QSprob qsx_;

  std::vector<mpq_class> qsx_rhs_;
  std::vector<LpRowSense> qsx_sense_;

  qsopt_ex::MpqArray ray_;  ///< Ray of the last infeasible solution

  friend void QsoptexCheckSatPartialSolution(mpq_QSdata const *prob, mpq_t *x, const mpq_t infeas, const mpq_t delta,
                                             void *data);
};

}  // namespace dlinear
