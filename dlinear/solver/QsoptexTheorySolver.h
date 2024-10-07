/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * QsoptexTheorySolver class.
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
/**
 * QSopt_ex is an exact LP solver written in C.
 * It uses the technique of precision boosting to efficiently solve LPs exactly.
 */
class QsoptexTheorySolver : public TheorySolver {
 public:
  explicit QsoptexTheorySolver(PredicateAbstractor &predicate_abstractor,
                               const std::string &class_name = "QsoptexTheorySolver");
  ~QsoptexTheorySolver() override;

  void AddVariable(const Variable &var) override;
  void AddLiterals() override;
  void Consolidate(const Box &box) override;

 protected:
  void UpdateModelBounds() override;
  void UpdateModelSolution() override;
  void UpdateExplanation(LiteralSet &explanation) override;

  /** Set the bounds of the variables in the LP solver.  */
  void EnableQsxVarBound();
  /**
   * Enable the @p qsx_row row for the LP solver.
   *
   * The truth value and the free variables are collected from the state of the solver.
   * @pre The row's coefficients must have been set correctly before calling this function
   * @pre The row's truth value must have been updated correctly
   * @pre The row's free variables must have been updated correctly
   * @param qsx_row index of the row to enable
   */
  void EnableQsxRow(int qsx_row);
  /**
   * Enable the @p qsx_row row for the LP solver.
   * @pre The row's coefficients must have been set correctly before calling this function
   * @param qsx_row index of the row to enable
   * @param truth truth value of the row
   */
  virtual void EnableQsxRow(int qsx_row, bool truth) = 0;

  /**
   * Disable all disabled qsx rows from the LP solver.
   *
   * Whether a row is disabled or not is determined by the @ref theory_row_state_ field,
   * where a true value means the row is enabled and a false value means the row is disabled.
   */
  void DisableQsxRows();
  /**
   * Parse a @p formula and set the correct coefficients of decisional variables in the @p qsx_row row.
   *
   * It will store the rhs term in @ref qsx_rhs_ and update the @p qsx_row with the parsed coefficients.
   * @param formula symbolic formula representing the row
   * @param qsx_row index of the row to update
   */
  void SetRowCoeff(const Formula &formula, int qsx_row);

  /**
   * Set the coefficient of @p var on the @p qsx_row row.
   * @param qsx_row row to update with the coefficient
   * @param var variable to set the coefficient for
   * @param value value to set the coefficient to
   */
  void SetQsxVarCoeff(int qsx_row, const Variable &var, const mpq_class &value);

  /**
   * Set the objective coefficient of @p var to @p value.
   * @param var variable to set the objective coefficient for
   * @param value value of the objective coefficient
   */
  void SetQsxVarObjCoeff(const Variable &var, const mpq_class &value);

  void SetLinearObjective(const Expression &expr);
  void ClearLinearObjective();

  // Exact LP solver (QSopt_ex)
  mpq_QSprob qsx_;

  std::vector<mpq_class> qsx_rhs_;     ///< Right-hand side of the constraints
  std::vector<LpRowSense> qsx_sense_;  ///< Sense of the constraints

  qsopt_ex::MpqArray ray_;  ///< Ray of the last infeasible solution
  qsopt_ex::MpqArray x_;    ///< Solution vector
};

void QsoptexCheckSatPartialSolution(mpq_QSdata const *prob, mpq_t *x, const mpq_t infeas, const mpq_t delta,
                                    void *data);
}  // namespace dlinear
