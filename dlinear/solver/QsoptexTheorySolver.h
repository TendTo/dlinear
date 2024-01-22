//
// Created by c3054737 on 15/01/24.
//
#pragma once

#include <vector>

#include "dlinear/libs/qsopt_ex.h"
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
  explicit QsoptexTheorySolver(PredicateAbstractor &predicate_abstractor, const Config &config = Config{});
  ~QsoptexTheorySolver() override;

  void AddVariable(const Variable &var) override;
  void Reset(const Box &box) override;

 protected:
  void SetLinearObjective(const Expression &expr);
  void ClearLinearObjective();

  void UpdateModelBounds() override;
  void UpdateExplanation(LiteralSet &explanation) override;
  void UpdateExplanation(const qsopt_ex::MpqArray &ray, LiteralSet &explanation) const;

  void SetQSXVarCoef(int qsx_row, const Variable &var, const mpq_class &value);
  void SetQSXVarObjCoef(const Variable &var, const mpq_class &value);
  bool SetQSXVarBound(const Bound &bound, int qsx_col);

  bool continuous_output_;
  bool with_timings_;

  // Exact LP solver (QSopt_ex)
  mpq_QSprob qsx_;

  std::vector<mpq_class> qsx_rhs_;
  std::vector<LpRowSense> qsx_sense_;

  friend void QsoptexCheckSatPartialSolution(mpq_QSdata const *prob, mpq_t *x, const mpq_t infeas, const mpq_t delta,
                                             void *data);
};

}  // namespace dlinear
