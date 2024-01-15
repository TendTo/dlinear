//
// Created by c3054737 on 15/01/24.
//
#pragma once

#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/solver/TheorySolver.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

extern "C" void QsoptexCheckSatPartialSolution(mpq_QSdata const *prob, mpq_t *x, const mpq_t infeas, const mpq_t delta,
                                               void *data);

class QsoptexTheorySolver : public TheorySolver {
 public:
  explicit QsoptexTheorySolver(PredicateAbstractor &predicate_abstractor, const Config &config = Config{});

  void AddLiteral(const Literal &lit) override;
  void AddVariable(const Variable &var) override;
  void EnableLiteral(const Literal &lit) override;
  SatResult CheckSat(const Box &box, mpq_class *actual_precision) override;
  void Reset(const Box &box) override;

 private:
  void SetLinearObjective(const Expression &expr);
  void ClearLinearObjective();

  void SetQSXVarCoef(int qsx_row, const Variable &var, const mpq_class &value);
  void SetQSXVarObjCoef(const Variable &var, const mpq_class &value);
  void SetQSXVarBound(const Variable &var, char type, const mpq_class &value);

  bool continuous_output_;
  bool with_timings_;

  // Exact LP solver (QSopt_ex)
  mpq_QSprob qsx_;

  std::vector<mpq_class> qsx_rhs_;
  std::vector<char> qsx_sense_;

  friend void QsoptexCheckSatPartialSolution(mpq_QSdata const *prob, mpq_t *x, const mpq_t infeas, const mpq_t delta,
                                             void *data);
};

}  // namespace dlinear
