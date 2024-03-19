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
#include "dlinear/util/Stats.h"

namespace dlinear {

/**
 * Theory solver class.
 *
 * Base class for theory solvers.
 * Theory solvers pick up the literals from the SAT solver and check whether the assignment is satisfiable within
 * the theory.
 * If that is not the case, they will produce an explanation to guide the SAT solver and find a new assignment.
 * This class has to be inherited and implemented by the specific theory solvers.
 */
class TheorySolver {
 public:
  using Bound = std::tuple<const Variable &, LpColBound, const mpq_class &>;
  /**
   * Construct a new Theory Solver object.
   *
   * The @p predicate_abstractor is shared between the theory solver and the SAT solver, in order to have a common
   * understanding of the literals.
   * @param predicate_abstractor predicate abstractor linking boolean literals to theory literals
   * @param config configuration of the theory solver
   */
  explicit TheorySolver(const PredicateAbstractor &predicate_abstractor, const Config &config = Config{});
  /**
   * Construct a new Theory Solver object.
   *
   * The @p predicate_abstractor is shared between the theory solver and the SAT solver, in order to have a common
   * understanding of the literals.
   * The @p class_name is used to identify the theory solver in the logs.
   * @param class_name name of the subclass of the theory solver used
   * @param predicate_abstractor predicate abstractor linking boolean literals to theory literals
   * @param config  configuration of the theory solver
   */
  TheorySolver(const std::string &class_name, const PredicateAbstractor &predicate_abstractor,
               const Config &config = Config{});
  virtual ~TheorySolver() = default;

  /**
   * Add a vector of literals to the theory solver.
   *
   * Each literal is formed by a variable that corresponds to a theory formula inside the PredicateAbstractor,
   * and the truth value (sense) of such literal
   * @param theory_literals vector of literals
   */
  void AddLiterals(const std::vector<Literal> &theory_literals);
  /**
   * Add a Literal to the theory solver.
   *
   * A Literal is formed by a variable that corresponds to a theory formula inside the PredicateAbstractor,
   * and the truth value (sense) of such literal
   * @param lit literal to be added
   */
  virtual void AddLiteral(const Literal &lit) = 0;
  /**
   * Add a variable (column) to the theory solver.
   * @param var variable to add
   */
  virtual void AddVariable(const Variable &var) = 0;
  /**
   * Activate the literals that have previously been added to the theory solver.
   * @param theory_literals vector of literals to be activated
   * @return a vector of explanations with the literals that correspond to the conflicting bounds
   */
  std::vector<LiteralSet> EnableLiterals(const std::vector<Literal> &theory_literals);
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
  virtual std::vector<LiteralSet> EnableLiteral(const Literal &lit) = 0;

  /**
   * Get a model that satisfies all the constraints of the theory
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

  /**
   * Get the statistics of the theory solver.
   * @return statistics of the theory solver
   */
  const IterationStats &stats() const { return stats_; }

 protected:
  using Violation = TheorySolverBoundVector::BoundIterator;  ///< Bound iterator over some violated bounds
  /**
   * Check whether the formula is a simple relational bound.
   *
   * A simple relational bound is a formula in the form:
   * @f[
   * a \leq b \\
   * a < b \\
   * a \geq b \\
   * a > b \\
   * a = b \\
   * a \neq b \\
   * @f]
   * Where @f$ a @f$ is a variable and @f$ b @f$ is a constant or vice versa.
   * @param formula symbolic formula to check
   * @return true if the formula is a simple relational bound
   * @return false if the formula is not a simple relational bound
   */
  static bool IsSimpleBound(const Formula &formula);
  /**
   * Check whether the formula is a simple relational bound with an equality operator (@f$ a = b @f$).
   * @param formula symbolic formula to check
   * @param truth whether to consider the formula as it is (true) or to invert it (false)
   * @return true if the formula respects the condition
   * @return false if the formula does not respect the condition
   * @see IsSimpleBound for more information about simple relational bounds
   */
  static bool IsEqualTo(const Formula &formula, bool truth = true);
  /**
   * Check whether the formula is a simple relational bound with a non-equality operator (@f$ a \neq b @f$).
   * @param formula symbolic formula to check
   * @param truth whether to consider the formula as it is (true) or to invert it (false)
   * @return true if the formula respects the condition
   * @return false if the formula does not respect the condition
   * @see IsSimpleBound for more information about simple relational bounds
   */
  static bool IsNotEqualTo(const Formula &formula, bool truth = true);
  /**
   * Check whether the formula is a simple relational bound with a greater than operator (@f$ a > b @f$).
   * @param formula symbolic formula to check
   * @param truth whether to consider the formula as it is (true) or to invert it (false)
   * @return true if the formula respects the condition
   * @return false if the formula does not respect the condition
   * @see IsSimpleBound for more information about simple relational bounds
   */
  static bool IsGreaterThan(const Formula &formula, bool truth = true);
  /**
   * Check whether the formula is a simple relational bound with a less than operator (@f$ a < b @f$).
   * @param formula symbolic formula to check
   * @param truth whether to consider the formula as it is (true) or to invert it (false)
   * @return true if the formula respects the condition
   * @return false if the formula does not respect the condition
   * @see IsSimpleBound for more information about simple relational bounds
   */
  static bool IsLessThan(const Formula &formula, bool truth = true);
  /**
   * Check whether the formula is a simple relational bound with a less than or equal to operator (@f$ a \ge b @f$).
   * @param formula symbolic formula to check
   * @param truth whether to consider the formula as it is (true) or to invert it (false)
   * @return true if the formula respects the condition
   * @return false if the formula does not respect the condition
   * @see IsSimpleBound for more information about simple relational bounds
   */
  static bool IsGreaterThanOrEqualTo(const Formula &formula, bool truth = true);
  /**
   * Check whether the formula is a simple relational bound with a less than or equal to operator (@f$ a \le b @f$).
   * @param formula symbolic formula to check
   * @param truth whether to consider the formula as it is (true) or to invert it (false)
   * @return true if the formula respects the condition
   * @return false if the formula does not respect the condition
   * @see IsSimpleBound for more information about simple relational bounds
   */
  static bool IsLessThanOrEqualTo(const Formula &formula, bool truth = true);

  /**
   * Use the @p violation of the bounds to produce an explanation for the SAT solver.
   * @param violation violated bounds
   * @param theory_bound bound of the theory solver that caused the violation
   * @return vector of explanations with the literals that correspond to the conflicting bounds
   */
  [[nodiscard]] std::vector<LiteralSet> TheoryBoundsToExplanations(Violation violation, int theory_bound) const;
  /**
   * Use the @p violation of the bounds to produce an explanation for the SAT solver.
   * @param violation violated bounds
   * @param theory_bound bound that caused the violation
   * @param[out] explanations vector of explanations with the literals that correspond to the conflicting bounds
   */
  void TheoryBoundsToExplanations(Violation violation, int theory_bound, std::vector<LiteralSet> explanations) const;
  /**
   * Gather the bounds of the @p theory_col and produce an explanation for the SAT solver.
   * @param theory_col column of the theory solver the bounds are associated with
   * @param active whether to only consider the active bounds (true) or include the inactive ones as well (false)
   * @param[out] explanation set of literals that correspond to the conflicting bounds
   */
  void TheoryBoundsToExplanation(int theory_col, bool active, LiteralSet &explanation) const;

  /**
   * Use the @p violation of the bounds to produce an explanation for the SAT solver.
   *
   * Unlike @ref TheoryBoundsToExplanations, this method will consider the rows indexes instead of the bound indexes.
   * @param violation violated bounds
   * @param theory_row row of the theory solver that caused the violation
   * @return vector of explanations with the literals that correspond to the conflicting bounds
   */
  [[nodiscard]] std::vector<LiteralSet> TheoryRowBoundsToExplanations(Violation violation, int theory_row) const;
  /**
   * Use the @p violation of the bounds to produce an explanation for the SAT solver.
   *
   * Unlike @ref TheoryBoundsToExplanations, this method will consider the rows indexes instead of the bound indexes.
   * @param violation violated bounds
   * @param theory_row row of the theory solver that caused the violation
   * @param explanations vector of explanations with the literals that correspond to the conflicting bounds
   */
  void TheoryRowBoundsToExplanations(Violation violation, int theory_row, std::vector<LiteralSet> &explanations) const;
  /**
   * Gather the bounds of the @p theory_col and produce an explanation for the SAT solver.
   *
   * Unlike @ref TheoryBoundsToExplanations, this method will consider the rows indexes instead of the bound indexes.
   * @param theory_col column of the theory solver the bounds are associated with
   * @param active whether to only consider the active bounds (true) or include the inactive ones as well (false)
   * @param[out] explanation set of literals that correspond to the conflicting bounds
   */
  void TheoryRowBoundsToExplanation(int theory_col, bool active, LiteralSet &explanation) const;

  /**
   * Get the indexes of the violated bounds.
   * @param violation violated bounds
   * @param[out] bound_idxs set of indexes of the bounds
   */
  static void TheoryBoundsToBoundIdxs(Violation violation, std::set<int> &bound_idxs);
  /**
   * Get all the indexes of the bounds that are associated with the @p theory_col.
   * @param theory_col theory column the bounds are associated with
   * @param active whether to only consider the active bounds (true) or include the inactive ones as well (false)
   * @param[out] bound_idxs set of indexes of the bounds
   */
  void TheoryBoundsToBoundIdxs(int theory_col, bool active, std::set<int> &bound_idxs) const;

  /**
   * Generate a tuple (var, type, value) that represents a bound on the variable.
   *
   * - var: theory variable the bound is associated with
   * - type: the type of bound:
   * @f[
   * \begin{gather*}
   *     \text{B}  & \rightarrow & b \leq       & x & \leq b      \\
   *     \text{SL} & \rightarrow & lb <         & x &             \\
   *     \text{L}  & \rightarrow & lb \leq      & x &             \\
   *     \text{SU} & \rightarrow & \            & x & < ub        \\
   *     \text{U}  & \rightarrow & \            & x & \leq ub     \\
   *     \text{F}  & \rightarrow & -\infty \leq & x & \leq \infty \\
   * \end{gather*}
   * @f]
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
   * Use the result from the theory solver to update the explanation with the conflict that has been detected.
   *
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

  const PredicateAbstractor &predicate_abstractor_;  ///< Predicate abstractor used to create the theory solver

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

  IterationStats stats_;  ///< Statistics of the theory solver
};

}  // namespace dlinear
