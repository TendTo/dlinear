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
  explicit TheorySolver(const PredicateAbstractor &predicate_abstractor, const Config &config = Config{});
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
  static bool IsEqualTo(const Formula &formula, bool truth);
  static bool IsNotEqualTo(const Formula &formula, bool truth);
  static bool IsGreaterThan(const Formula &formula, bool truth);
  static bool IsLessThan(const Formula &formula, bool truth);
  static bool IsGreaterThanOrEqualTo(const Formula &formula, bool truth);
  static bool IsLessThanOrEqualTo(const Formula &formula, bool truth);

  int simplex_sat_phase_;
  double precision_;

  const PredicateAbstractor &predicate_abstractor_;

  std::map<Variable::Id, int> var_to_theory_col_;  ///< Variable ⇔ theory column.
                                                   ///< The Variable is the one created by the PredicateAbstractor
                                                   ///< The column is the one used by the theory solver.
  std::map<int, Variable> theory_col_to_var_;      ///< Theory column ⇔ Variable.
                                                   ///< The column is the one used by the theory solver.
                                                   ///< The Variable is the one created by the PredicateAbstractor

  std::map<Variable::Id, std::tuple<bool, int, int>>
      lit_to_theory_row_;  ///< Literal ⇔ theory row.
                           ///< The tuple contains the truth value of the literal when it was added to the LP solver
                           ///< Up to two rows that map to the constraint the theory solver will check.
  std::vector<Literal> theory_row_to_lit_;  ///< Theory row ⇔ Literal
                                            ///< The row is the constraint used by the theory solver.
                                            ///< The tuple contains the truth value of the literal when it was first
                                            ///< added to the LP solver,

  Box model_;  ///< Model produced by the theory solver
};

}  // namespace dlinear
