/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * TheorySolver class.
 */
#pragma once

#include <map>
#include <set>
#include <string>
#include <tuple>
#include <vector>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/BoundIterator.h"
#include "dlinear/solver/BoundPreprocessor.h"
#include "dlinear/solver/LpColBound.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Stats.h"

namespace dlinear {

/**
 * Base class for theory solvers.
 *
 * Theory solvers pick up the literals assignments from the SAT solver
 * and check whether the assignment is satisfiable within the theory.
 * If that is not the case, they will produce an explanation to guide the SAT solver and find a new assignment.
 * This class has to be inherited and implemented by the specific theory solvers.
 */
class TheorySolver {
 public:
  using Bound = std::tuple<const Variable &, LpColBound, const mpq_class &>;  ///< Bound on the variable
  using Violation = BoundIterator;            ///< Bound iterator over some violated bounds
  using Explanations = std::set<LiteralSet>;  ///< Set of explanations of the conflict
  /**
   * Construct a new Theory Solver object.
   *
   * The @p predicate_abstractor is shared between the theory solver and the SAT solver, in order to have a common
   * understanding of the literals.
   * The @p class_name is used to identify the theory solver in the logs.
   * @note The @p predicate abstractor will share its configuration with the theory solver.
   * @param class_name name of the subclass of the theory solver used
   * @param predicate_abstractor predicate abstractor linking boolean literals to theory literals. It is shared between
   * the theory solver and the SAT solver
   */
  explicit TheorySolver(const PredicateAbstractor &predicate_abstractor,
                        const std::string &class_name = "TheorySolver");
  virtual ~TheorySolver() = default;

  /**
   * Add a vector of literals to the theory solver.
   *
   * Each literal is formed by a variable that corresponds to a theory formula inside the PredicateAbstractor
   */
  virtual void AddLiterals();
  /**
   * Add a Literal to the theory solver.
   *
   * A Literal is formed by a variable that corresponds to a theory formula inside the PredicateAbstractor
   * and the formula itself
   * @param formula_var boolean variable that corresponds to the theory formula
   * @param formula symbolic formula that represents the theory formula
   */
  virtual void AddLiteral(const Variable &formula_var, const Formula &formula) = 0;
  /**
   * Add the fixed literals to the theory solver.
   *
   * This means that, for the model to be sat, these literals will never change their assignment.
   * This allows for slight optimizations
   * (e.g. their bound can be computed once, at the beginning of the run instead of at each iteration)
   * @param fixed_literals set of fixed literals
   */
  virtual Explanations PreprocessFixedLiterals(const LiteralSet &fixed_literals);
  /**
   * Add a variable (column) to the theory solver.
   * @param var variable to add
   */
  virtual void AddVariable(const Variable &var) = 0;
  /**
   * Activate the literals that have previously been added to the theory solver.
   * @param theory_literals vector of literals to be activated
   * @return a set of explanations with the literals that correspond to the conflicting bounds
   */
  Explanations EnableLiterals(std::span<const Literal> theory_literals);
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
  virtual Explanations EnableLiteral(const Literal &lit) = 0;

  /** @getter{model that satisfies all the constraints, TheorySolver} */
  [[nodiscard]] const Box &model() const;
  /** @getter{configuration, TheorySolver} */
  [[nodiscard]] const Config &config() const { return config_; }
  /** @getter{predicate abstractor, TheorySolver} */
  [[nodiscard]] const PredicateAbstractor &predicate_abstractor() const { return predicate_abstractor_; }
  /** @getter{map of variables to the theory columns, TheorySolver} */
  [[nodiscard]] const std::map<Variable::Id, int> &var_to_theory_col() const { return var_to_theory_col_; }
  /** @getter{map of theory columns to the variables, TheorySolver} */
  [[nodiscard]] const std::vector<Variable> &theory_col_to_var() const { return theory_col_to_var_; }
  /** @getter{map of literals to the theory rows, TheorySolver} */
  [[nodiscard]] const std::map<Variable::Id, int> &lit_to_theory_row() const { return lit_to_theory_row_; }
  /** @getter{map of theory rows to the literals, TheorySolver} */
  [[nodiscard]] const std::vector<Literal> &theory_row_to_lit() const { return theory_row_to_lit_; }
  /** @getter{bounds of each theory variable, TheorySolver} */
  [[nodiscard]] const BoundVectorMap &theory_bounds() const { return preprocessor_.theory_bounds(); }
  /** @getter{fixed bounds of each theory variable, TheorySolver} */
  [[nodiscard]] const BoundVectorMap &fixed_theory_bounds() const { return fixed_preprocessor_.theory_bounds(); }
  /** @getter{bound preprocessor, TheorySolver} */
  [[nodiscard]] const BoundPreprocessor &preprocessor() const { return preprocessor_; }
  /** @getsetter{bound preprocessor, TheorySolver} */
  [[nodiscard]] BoundPreprocessor &m_preprocessor() { return preprocessor_; }
  /** @getter{fixed bound preprocessor, TheorySolver} */
  [[nodiscard]] const BoundPreprocessor &fixed_preprocessor() const { return fixed_preprocessor_; }
  /** @getsetter{fixed bound preprocessor, TheorySolver} */
  [[nodiscard]] BoundPreprocessor &m_fixed_preprocessor() { return fixed_preprocessor_; }
  /** @getter{number of rows, TheorySolver} */
  [[nodiscard]] std::size_t theory_row_count() const { return theory_row_to_lit_.size(); }
  /** @getter{number of columns, TheorySolver} */
  [[nodiscard]] std::size_t theory_col_count() const { return theory_col_to_var_.size(); }
  /** @getter{vector of enabled literals, TheorySolver} */
  [[nodiscard]] std::set<Literal> enabled_literals() const;

  /**
   * Check the satisfiability of the theory.
   *
   * Run the internal LP solver to check whether the underlying linear programming problem is feasible.
   * If it is, SAT will be returned, along with the actual precision required to obtain that result.
   * Otherwise, UNSAT will be returned, along with an explanation of the conflict.
   * In that case, the precision will remain the same as the one passed as input.
   * @param box current box with the bounds for the variables, including the boolean ones
   * @param[in,out] actual_precision desired precision. It will be updated with the actual precision if SAT is returned
   * @param[out] explanations set of sets of literals that explain the conflict if UNSAT is returned
   * @return SAT if the problem is feasible, along with the actual precision required to obtain that result and the
   * model
   * @return UNSAT if the problem is infeasible, along with an explanation of the conflict
   */
  SatResult CheckSat(const Box &box, mpq_class *actual_precision, std::set<LiteralSet> &explanations);
  /**
   * Check the satisfiability of the theory.
   *
   * Called by @ref CheckSat.
   * Run the internal LP solver to check whether the underlying linear programming problem is feasible.
   * If it is, SAT will be returned, along with the actual precision required to obtain that result.
   * Otherwise, UNSAT will be returned, along with an explanation of the conflict.
   * In that case, the precision will remain the same as the one passed as input.
   * @param[in,out] actual_precision desired precision. It will be updated with the actual precision if SAT is returned
   * @param[out] explanations set of sets of literals that explain the conflict if UNSAT is returned
   * @return SAT if the problem is feasible, along with the actual precision required to obtain that result and the
   * model
   * @return UNSAT if the problem is infeasible, along with an explanation of the conflict
   */
  virtual SatResult CheckSatCore(mpq_class *actual_precision, std::set<LiteralSet> &explanations) = 0;

  /**
   * Consolidate the solver.
   *
   * This method must be called after all the literals have been added to the solver and before calling
   * any other method.
   * Once the solver has been consolidated, no more literals can be added to it.
   * A previously added literal can be enabled using the @ref EnableLiteral method and disabled with @ref Reset.
   * @note A solver can be consolidated only once.
   * If you need to change the variables or constraints, you must create a new theory solver.
   * @param box box with the bounds for the variables
   */
  virtual void Consolidate(const Box &box);

  /**
   * Reset the linear problem.
   *
   * All constraints' state will be set to @p disabled and the bounds for each variable will be cleared.
   * @note The variables and constraints themselves will not be modified.
   * If you need to change them, you must create a new theory solver.
   */
  virtual void Reset();

  /**
   * Get the statistics of the theory solver.
   * @return statistics of the theory solver
   */
  [[nodiscard]] const IterationStats &stats() const { return stats_; }

#ifndef NDEBUG
  void DumpEnabledLiterals();
#endif

 protected:
  /** Enum used to describe how the bounds on a variable participate in the infeasibility result of an LP problem */
  enum class BoundViolationType {
    NO_BOUND_VIOLATION,     ///< The bounds of the variable have no role in the infeasibility
    LOWER_BOUND_VIOLATION,  ///< The lower bound is involved in the infeasibility
    UPPER_BOUND_VIOLATION,  //< The upper bound is involved in the infeasibility
  };

  void BoundsToTheoryRows(const Variable &var, const mpq_class &value, std::set<int> &theory_rows) const;
  void BoundsToTheoryRows(const Variable &var, BoundViolationType type, std::set<int> &bound_idxs) const;
  /**
   * Update the model with the solution obtained from the LP solver.
   *
   * The model with show an assignment that satisfies all the theory literals.
   * @pre the lp solver must have found a feasible solution
   */
  virtual void UpdateModelSolution() = 0;
  /**
   * Update each variable in the model with the bounds passed to the theory solver.
   * @note there is no check in place on whether the bounds are inverted or the constraints
   * satisfied.
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
   * Use the result from the theory solver to update the explanations with the conflict that has been detected.
   *
   * A new explanations will be added to the current set of explanations.
   * This will allow the SAT solver to find a new assignment without the conflict.
   * @param explanations set of explanations the new conflicting clauses will be added to
   */
  void UpdateExplanations(Explanations &explanations);

  const Config &config_;  ///< Configuration of the theory solver

  bool is_consolidated_;  ///< Whether the solver has been consolidated.
                          ///< This method must be called after all the literals have been added to the solver.

  const PredicateAbstractor &predicate_abstractor_;  ///< Predicate abstractor used to create the theory solver

  std::map<Variable::Id, int> var_to_theory_col_;  ///< Variable ⇔ theory column.
                                                   ///< The Variable is the one created by the PredicateAbstractor
                                                   ///< The column is the one used by the theory solver.
  std::vector<Variable> theory_col_to_var_;        ///< Theory column ⇔ Variable.
                                                   ///< The column is the one used by the theory solver.
                                                   ///< The Variable is the one created by the PredicateAbstractor
  std::map<Variable::Id, int> lit_to_theory_row_;  ///< Literal ⇔ theory row.
                                                   ///< The literal is the one created by the PredicateAbstractor
                                                   ///< The row is the constraint used by the theory solver.
  std::vector<Literal> theory_row_to_lit_;         ///< Theory row ⇔ Literal
                                                   ///< The row is the constraint used by the theory solver.
                                                   ///< The literal is the one created by the PredicateAbstractor.
                                                   ///< It may not contain simple bounds
  std::vector<bool> theory_rows_state_;            ///< Whether each theory row is enabled or not.

  ///< It also verifies that the bounds are consistent every time a new one is added.

  BoundPreprocessor fixed_preprocessor_;  ///< Preprocessor for the bounds. Only computed on fixed literal theories.
  BoundPreprocessor preprocessor_;        ///< Preprocessor for the bounds.
  ///< Propagates the bounds through simple expressions to produce a precise explanation of the conflict
  ///< without invoking the LP solver.
  //< It will be reset to the @ref fixed_preprocessor_ at every iteration.

  Box model_;  ///< Model produced by the theory solver

  IterationStats stats_;  ///< Statistics of the theory solver
};

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::TheorySolver::Bound)

#endif
