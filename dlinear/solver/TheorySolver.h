//
// Created by c3054737 on 11/01/24.
//
#pragma once

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"

namespace dlinear {

class TheorySolver {
 public:
  explicit TheorySolver(PredicateAbstractor &predicate_abstractor, const Config &config = Config{});
  virtual ~TheorySolver() = default;

  /**
   * Add a vector of literals to the theory solver.
   * Each literal is formed by a variable that corresponds to a theory formula inside the PredicateAbstractor,
   * and the truth value (sense) of such literal
   *
   * @param theory_literals vector of literals
   */
  void AddLiterals(const std::vector<Literal> &theory_literals);
  /**
   * Add a Literal to the theory solver.
   * A Literal is formed by a variable that corresponds to a theory formula inside the PredicateAbstractor,
   * and the truth value (sense) of such literal
   *
   * @param lit literal to be added
   */
  virtual void AddLiteral(const Literal &lit) = 0;
  /**
   * Add a variable (column) to the theory solver.
   *
   * @param var variable to add
   */
  virtual void AddVariable(const Variable &var) = 0;
  /**
   * Activate the literals that have previously been added to the theory solver.
   *
   * @param theory_literals vector of literals to be activated
   */
  void EnableLiterals(const std::vector<Literal> &theory_literals);
  /**
   * Activate the literal that had previously been added to the theory solver
   * @param lit literal to activate
   */
  virtual void EnableLiteral(const Literal &lit) = 0;

  /**
   * Get a model that satisfies all the constraints of the theory
   *
   * @return model that satisfies all the constraints of the theory
   */
  [[nodiscard]] const Box &GetModel() const;

  [[nodiscard]] const std::map<int, Variable> &GetLinearVarMap() const;

  virtual SatResult CheckSat(const Box &box, mpq_class *actual_precision) = 0;

  /**
   * Reset the linear problem, disabling all constraints and bounds to the ones
   * in the box.
   *
   * @param box cox containing the bounds for the variables that will be applied to the theory solver
   */
  virtual void Reset(const Box &box) = 0;

 protected:
  static bool IsSimpleBound(const Formula &formula);
  static bool IsEqualToOrWhatever(const Formula &formula, bool truth);
  static bool IsNotEqualToOrWhatever(const Formula &formula, bool truth);
  static bool IsGreaterThanOrWhatever(const Formula &formula, bool truth);
  static bool IsLessThanOrWhatever(const Formula &formula, bool truth);

  int simplex_sat_phase_;
  PredicateAbstractor &predicate_abstractor_;

  std::map<Variable::Id, int> var_to_theory_col_;
  std::map<int, Variable> theory_col_to_var_;

  std::map<std::pair<Variable::Id, bool>, int> lit_to_theory_row_;
  std::vector<Literal> theory_row_to_lit_;

  Box model_;  ///< model produced by the theory solver
};

}  // namespace dlinear
