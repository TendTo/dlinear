/**
 * @file TheorySolver.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Base class for theory solvers.
 *
 * Theory solvers are used to solve the theory of a given logic.
 * When given an assignment from the SAT solver, they will check whether the assignment is satisfiable.
 * If that is not the case, they will produce an explanation to guide the SAT solver and find a new assignment.
 */
#pragma once

#include <map>
#include <optional>
#include <tuple>
#include <vector>

#include "dlinear/libs/gmp.h"
#include "dlinear/solver/LpColBound.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/solver/TheorySolverBoundVector.h"
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

  [[nodiscard]] const std::vector<Variable> &GetLinearVarMap() const;

  [[nodiscard]] size_t n_variables() const;

  /**
   * Check the satisfiability of the theory.
   *
   * Run the internal LP solver to check whether the underlying linear programming problem is feasible.
   * If it is, SAT will be returned, along with the actual precision required to obtain that result.
   * Otherwise, UNSAT will be returned, along with an explanation of the conflict.
   * In that case, the precision will remain the same as the one passed as input.
   * @param[in,out] box current box with the bounds for the variables. It will be updated with the model if SAT is
   * returned
   * @param[in,out] actual_precision desired precision. It will be updated with the actual precision if SAT is returned
   * @param[out] explanation set of literals that explain the conflict if UNSAT is returned
   * @return SAT if the problem is feasible, along with the actual precision required to obtain that result and the
   * model
   * @return UNSAT if the problem is infeasible, along with an explanation of the conflict
   */
  virtual SatResult CheckSat(const Box &box, mpq_class *actual_precision, LiteralSet &explanation) = 0;

  /**
   * Reset the linear problem.
   *
   * All constraints will be disabled and the bounds will be set to the ones in the box.
   * @note The variables and constraints will not be modified.
   * If you need to change the variables or constraints, you must create a new theory solver.
   * @param box cox containing the bounds for the variables that will be applied to the theory solver
   */
  virtual void Reset(const Box &box) = 0;

 protected:
  using Violation = TheorySolverBoundVector::Violation;
  static bool IsSimpleBound(const Formula &formula);
  static bool IsEqualTo(const Formula &formula, bool truth = true);
  static bool IsNotEqualTo(const Formula &formula, bool truth = true);
  static bool IsGreaterThan(const Formula &formula, bool truth = true);
  static bool IsLessThan(const Formula &formula, bool truth = true);
  static bool IsGreaterThanOrEqualTo(const Formula &formula, bool truth = true);
  static bool IsLessThanOrEqualTo(const Formula &formula, bool truth = true);

  [[nodiscard]] LiteralSet TheoryBoundsToExplanation(const Violation &violation) const;
  void TheoryBoundsToExplanation(const Violation &violation, LiteralSet &explanation) const;
  void TheoryBoundsToExplanation(int theory_col, LiteralSet &explanation) const;
  void TheoryBoundsToExplanation(int theory_col, mpq_class value, LiteralSet &explanation) const;

  void TheoryBoundsToBoundIdxs(int theory_col, std::set<int> &bound_idxs) const;
  void TheoryBoundsToBoundIdxs(int theory_col, mpq_class value, std::set<int> &bound_idxs) const;
  static void TheoryBoundsToBoundIdxs(const Violation &violation, std::set<int> &bound_idxs) ;

  /**
   * Generate a tuple (var, type, value) that represents a bound on the variable.
   *
   * - var: theory variable the bound is associated with
   * - type: the type of bound:
   *    - B:  value <= var <= value
   *    - SL: value <  var
   *    - L:  value <= var
   *    - SU:          var <  value
   *    - U:           var <= value
   *    - F:  -inf  <= var <= inf
   * - value: value of the bound
   * @param formula symbolic formula that represents a simple relational bound
   * @param truth whether the formula is to be interpreted as it is (true) or must be inverted (false)
   * @return tuple representing a bound
   */
  static Bound GetBound(const Formula &formula, bool truth = true);

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

  /**
   * Consolidate the solver.
   *
   * This method must be called after all the literals have been added to the solver and before calling
   * any other method.
   * Once the solver has been consolidated, no more literals can be added to it.
   * A previously added literal can be enabled using the @ref EnableLiteral method and disabled with @ref Reset.
   * @note A solver can be consolidated only once.
   * If you need to change the variables or constraints, you must create a new theory solver.
   */
  virtual void Consolidate();

  bool is_consolidated_;        ///< Whether the solver has been consolidated.
                                ///< This method must be called after all the literals have been added to the solver.
  int simplex_sat_phase_;       ///< Phase of the simplex algorithm
  double precision_;            ///< Precision used to check the satisfiability of the theory
  const bool needs_expansion_;  ///< Whether the formulas need to be expanded before building the LP constraints.
                                ///< - SMT2 files: the expansion is needed.
                                ///< - MPS files: the expansion is not needed.

  const PredicateAbstractor &predicate_abstractor_;

  std::map<Variable::Id, int> var_to_theory_col_;    ///< Variable ⇔ theory column.
                                                     ///< The Variable is the one created by the PredicateAbstractor
                                                     ///< The column is the one used by the theory solver.
  std::vector<Variable> theory_col_to_var_;          ///< Theory column ⇔ Variable.
                                                     ///< The column is the one used by the theory solver.
                                                     ///< The Variable is the one created by the PredicateAbstractor
  std::map<Variable::Id, int> lit_to_theory_row_;    ///< Literal ⇔ theory row.
                                                     ///< The literal is the one created by the PredicateAbstractor
                                                     ///< The row is the constraint used by the theory solver.
  std::vector<Literal> theory_row_to_lit_;           ///< Theory row ⇔ Literal
                                                     ///< The row is the constraint used by the theory solver.
                                                     ///< The literal is the one created by the PredicateAbstractor.
                                                     ///< It may not contain simple bounds
  std::vector<Literal> theory_bound_to_lit_;         ///< Theory bound ⇔ Literal
                                                     ///< The bound is the constraint on the values of the variables.
                                                     ///< The literal is the one created by the PredicateAbstractor.
                                                     ///< It can only contain simple bounds
  std::map<Variable::Id, int> lit_to_theory_bound_;  ///< Literal ⇔ theory bound.
                                                     ///< The literal is the one created by the PredicateAbstractor
                                                     ///< The bound is the constraint on the values of the variables.
                                                     ///< It can only contain simple bounds
  TheorySolverBoundVectorVector theory_bounds_;      ///< Theory bounds.
                                                     ///< The bounds are the constraints on the values of the variables.
  ///< It also verifies that the bounds are consistent every time a new one is added.

  Box model_;  ///< Model produced by the theory solver
};

}  // namespace dlinear
