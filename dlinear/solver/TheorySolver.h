//
// Created by c3054737 on 11/01/24.
//
#pragma once

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"

namespace dlinear {

class TheorySolver {
 public:
  explicit TheorySolver(const Config &config = Config{});
  virtual ~TheorySolver() = default;

  void AddFormula(const Formula &f);

  virtual void AddTheoryVariable(const Variable &var) = 0;

  void EnableTheoryLiterals(const std::vector<Literal> &theory_literals,
                            const VarToTheoryLiteralMap &var_to_theory_literals);
  virtual void EnableTheoryLiteral(const Literal &lit, const VarToTheoryLiteralMap &var_to_theory_literals) = 0;

  /**
   * Get a model that satisfies all the constraints of the theory
   *
   * @return model that satisfies all the constraints of the theory
   */
  [[nodiscard]] const Box &GetModel() const;

  [[nodiscard]] const std::map<int, Variable> &GetLinearVarMap() const;

  virtual SatResult CheckSat(const Box &box, mpq_class *actual_precision) = 0;

 protected:
  static bool IsSimpleBound(const Formula &formula);
  static bool IsEqualToOrWhatever(const Formula &formula, bool truth);
  static bool IsNotEqualToOrWhatever(const Formula &formula, bool truth);
  static bool IsGreaterThanOrWhatever(const Formula &formula, bool truth);
  static bool IsLessThanOrWhatever(const Formula &formula, bool truth);

  virtual void ResetLinearProblem(const Box &box) = 0;

  int simplex_sat_phase_;

  std::map<Variable::Id, int> var_to_theory_col_;
  std::map<int, Variable> theory_col_to_var_;

  std::map<std::pair<Variable::Id, bool>, int> lit_to_theory_row_;
  std::vector<Literal> theory_row_to_lit_;

  Box model_;  ///< model produced by the theory solver
};

}  // namespace dlinear
