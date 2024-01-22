//
// Created by c3054737 on 11/01/24.
//
#pragma once

#include <map>
#include <optional>
#include <tuple>
#include <vector>

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/LpColBound.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"

namespace dlinear {

class TheorySolver {
 public:
  using Bound = std::tuple<const Variable &, LpColBound, const mpq_class &>;

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
  std::optional<LiteralSet> EnableLiterals(const std::vector<Literal> &theory_literals);
  /**
   * Activate the literal that had previously been added to the theory solver.
   *
   * If the literal is a row inside the TheorySolver,
   * then the the corresponding constraint is activated by giving it the proper values.
   *
   * If the literal is a simple bound on the variable (column), some additional checks are made.
   * Theory solvers struggle to handle problems with inverted bounds.
   * It is convenient to have a method that checks them beforehand.
   * If at least a bound is inverted, the problem is UNSAT, since it is impossible to satisfy the constraint.
   * An explanation is produced and returned to the SAT solver.
   * @param lit literal to activate
   * @return an explanation with the literals that correspond to the conflicting bounds
   * @return an empty optional if no conflicts are detected at this step
   */
  virtual std::optional<LiteralSet> EnableLiteral(const Literal &lit) = 0;

  /**
   * Get a model that satisfies all the constraints of the theory
   *
   * @return model that satisfies all the constraints of the theory
   */
  [[nodiscard]] const Box &GetModel() const;

  [[nodiscard]] const std::map<int, Variable> &GetLinearVarMap() const;

  virtual SatResult CheckSat(const Box &box, mpq_class *actual_precision, LiteralSet &explanation) = 0;

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

  /**
   * Generate a tuple (var, type, value) that represents a bound on the variable.
   *
   * - var: theory variable the bound is associated with
   * - type: the type of bound:
   *    - B: value <= var <= value
   *    - L: value <= var
   *    - U:          var <= value
   *    - F: -inf  <= var <= inf
   * - value: value of the bound
   * @param formula symbolic formula that represents a simple relational bound
   * @param truth whether the formula is to be interpreted as it is (true) or must be inverted (false)
   * @return tuple representing a bound
   */
  static Bound GetBound(const Formula &formula, bool truth);

  /**
   * Update each variable in the model with the bounds passed to the theory solver.
   * @note there is no check in place on whether the bounds are inverted or the constraints satisfied.
   */
  virtual void UpdateModelBounds() = 0;

  /**
   * Use the result from the LP solver to update the explanation with the conflict that has been detected.
   * This will allow the SAT solver to find a new assignment without the conflict.
   * @warning The explanation will be cleared before adding the conflicting literals
   * @param explanation set conflicting clauses to be updated
   */
  virtual void UpdateExplanation(LiteralSet &explanation) = 0;

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
  std::vector<bool> theory_row_to_truth_;  ///< Theory row ⇔ truth value
                                           ///< The row is the constraint used by the theory solver.
                                           ///< The truth is the boolean assignment of the literal during this iteration
  std::vector<LiteralSet>
      theory_bound_to_explanation_;  ///< Theory bound ⇔ Explanation
                                     ///< The bound is used by the theory solver to limit a variable.
                                     ///< The explanation is the set of literals that explain why
                                     ///< the bound on the col (variable) is unsatisfiable

  Box model_;  ///< Model produced by the theory solver
};

}  // namespace dlinear
