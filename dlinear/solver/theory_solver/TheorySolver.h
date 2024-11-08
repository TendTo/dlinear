/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * TheorySolver class.
 */
#pragma once

#include <functional>
#include <memory>
#include <set>
#include <span>
#include <string>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/theory_solver/TheoryPreprocessor.h"
#include "dlinear/solver/theory_solver/TheoryPropagator.h"
#include "dlinear/solver/theory_solver/TheoryResult.h"
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
  /**
   * Construct a new Theory Solver object.
   *
   * The @p predicate_abstractor is shared between the theory solver and the SAT solver, in order to have a common
   * understanding of the literals.
   * The @p class_name is used to identify the theory solver in the logs.
   * @note The @p predicate abstractor will share its configuration with the theory solver.
   * @param predicate_abstractor predicate abstractor linking boolean literals to theory literals. It is shared between
   * the theory solver and the SAT solver and will determine the theory solver's configuration
   * @param class_name name of the subclass of the theory solver used
   */
  explicit TheorySolver(const PredicateAbstractor &predicate_abstractor,
                        const std::string &class_name = "TheorySolver");
  virtual ~TheorySolver() = default;

  /** Add all the literals in the @ref pa_ to the theory solver. */
  virtual void AddLiterals();
  /**
   * Add a vector of literals to the theory solver.
   *
   * Each literal is formed by a variable that corresponds to a theory formula inside the PredicateAbstractor
   */
  virtual void AddLiterals(std::span<const Literal> literals);
  /**
   * Add a Literal to the theory solver.
   *
   * A Literal is formed by a variable that corresponds to a theory formula inside the PredicateAbstractor
   * and the formula itself.
   * @param formula_var boolean variable that corresponds to the theory formula
   * @param formula symbolic formula that represents the theory formula
   */
  virtual void AddLiteral(const Variable &formula_var, const Formula &formula) = 0;
  /**
   * Preprocess the @p fixed_literals to ensure there is no trivial inconsistency which would lead to an early UNSAT.
   *
   * Fixed literals will never change the truth value assigned to them.
   * This allows for slight optimizations
   * (e.g. their bound can be computed once, at the beginning of the run instead of at each iteration).
   * Some quick preprocessing will be run to ensure that the @p fixed_literals are not trivially inconsistent.
   * If that is the case, an explanation is produced and used to invoke the @p conflict_cb .
   * @pre the literals must have been added to the theory solver with @ref AddLiteral
   * @param fixed_literals set of fixed literals
   * @param conflict_cb callback to be called when a conflict is detected. It will receive the explanation
   * @return true if no conflicts are detected at this step
   * @return false if a conflict is detected at this step
   */
  virtual bool PreprocessFixedLiterals(const LiteralSet &fixed_literals, const ConflictCallback &conflict_cb);
  /**
   * Add a variable to the theory solver.
   * @param var variable to add
   */
  virtual void AddVariable(const Variable &var) = 0;
  /**
   * Enable the @p theory_literals that have previously been added to the theory solver.
   *
   * Some quick preprocessing will be run to ensure that the @p theory_literals are not trivially inconsistent
   * with the current set of enabled literals.
   * If that is the case, an explanation is produced and used to invoke the @p conflict_cb .
   * @pre the literal must have been added to the theory solver with @ref AddLiteral
   * @param theory_literals vector of literals to be enabled
   * @param conflict_cb callback to be called when a conflict is detected. It will receive the explanation
   * @return true if no conflicts are detected at this step
   * @return false if a conflict is detected at this step
   */
  bool EnableLiterals(std::span<const Literal> theory_literals, const ConflictCallback &conflict_cb);
  /**
   * Enable the @p lit literal that had previously been added to the theory solver.
   *
   * Some quick preprocessing will be run to ensure that @p lit is not trivially inconsistent with the current
   * set of enabled literals.
   * If that is the case, an explanation is produced and used to invoke the @p conflict_cb .
   * @pre the literal must have been added to the theory solver with @ref AddLiteral
   * @param lit new literal to be enabled
   * @return true if no conflicts are detected at this step
   * @return false if a conflict is detected at this step
   */
  virtual bool EnableLiteral(const Literal &lit, ConflictCallback conflict_cb) = 0;

  /** @getter{model that satisfies all the constraints, TheorySolver} */
  [[nodiscard]] const Box &model() const;
  /** @getter{configuration, TheorySolver} */
  [[nodiscard]] const Config &config() const { return config_; }
  /** @getter{predicate abstractor, TheorySolver} */
  [[nodiscard]] const PredicateAbstractor &predicate_abstractor() const { return pa_; }
  /** @getter{vector of enabled literals, TheorySolver} */
  [[nodiscard]] virtual LiteralSet enabled_literals() const = 0;
  /** @getter{statistics, TheorySolver} */
  [[nodiscard]] const IterationStats &stats() const { return stats_; }

  /**
   * Check the satisfiability of the theory.
   *
   * Run the appropriate internal solver to check whether the model of enabled literals is valid within the theory.
   * If it is, SAT will be returned, along with the actual precision required to obtain that result.
   * Otherwise, UNSAT will be returned and the explanation produced is used to invoke the @p conflict_cb .
   * In that case, the precision will remain the same as the one passed as input.
   * @param[in,out] actual_precision desired precision. It will be updated with the actual precision if SAT is returned
   * @param conflict_cb callback to be called when a conflict is detected. It will receive the explanation
   * @return SAT if the problem is feasible, along with the actual precision required to obtain that result and the
   * model
   * @return UNSAT if the problem is infeasible, along with an explanation of the conflict
   * @return ERROR if an error occurred during the check
   */
  TheoryResult CheckSat(mpq_class *actual_precision, const ConflictCallback &conflict_cb);
  /**
   * Check the satisfiability of the theory.
   *
   * Called by @ref CheckSat.
   * Run the appropriate internal solver to check whether the model of enabled literals is valid within the theory.
   * If it is, SAT will be returned, along with the actual precision required to obtain that result.
   * Otherwise, UNSAT will be returned and the explanation produced is used to invoke the @p conflict_cb .
   * In that case, the precision will remain the same as the one passed as input.
   * @param[in,out] actual_precision desired precision. It will be updated with the actual precision if SAT is returned
   * @param conflict_cb callback to be called when a conflict is detected. It will receive the explanation
   * @return SAT if the problem is feasible, along with the actual precision required to obtain that result and the
   * model
   * @return UNSAT if the problem is infeasible, along with an explanation of the conflict
   * @return ERROR if an error occurred during the check
   */
  virtual TheoryResult CheckSatCore(mpq_class *actual_precision, ConflictCallback conflict_cb) = 0;

  /**
   * Consolidate the solver using the knowledge of the added literals.
   *
   * This method must be called after all the literals have been added to the solver and before calling
   * any other method.
   * Once the solver has been consolidated, no more literals can be added to it.
   * A previously added literal can be enabled using the @ref EnableLiteral method and disabled with @ref Backtrack.
   * @note A solver can be consolidated only once.
   * If you need to change the variables or constraints, you must create a new theory solver.
   * @param box box with the bounds for the variables, if any
   */
  virtual void Consolidate(const Box &box);

  /**
   * Disable all the enabled constraints of the theory solver, making it ready to run another iteration.
   *
   * All constraints' state will be disabled.
   * @note Variables and constraints added previously may not be removed or altered,
   * but they will need to be enabled again to be considered in the next iteration.
   * If you need to change them, you must create a new theory solver.
   */
  virtual void Backtrack();

#ifndef NDEBUG
  virtual void DumpEnabledLiterals() = 0;
#endif

 protected:
  /**
   * Update the model with the solution obtained from the LP solver.
   *
   * The model with show an assignment that satisfies all the theory literals.
   * @pre the lp solver must have found a feasible solution
   */
  virtual void UpdateModelSolution() = 0;

  const Config &config_;           ///< Configuration of the theory solver
  bool is_consolidated_;           ///< Whether the solver has been consolidated.
                                   ///< It must be true before running the solver or enabling literals
  const PredicateAbstractor &pa_;  ///< Predicate abstractor mapping boolean vars to theory literals
  Box model_;                      ///< Model produced by the theory solver
  IterationStats stats_;           ///< Statistics of the theory solver

  std::unique_ptr<TheoryPreprocessor> preprocessor_;  ///< Preprocessor to handle the theory constraints
  std::unique_ptr<TheoryPropagator> propagator_;      ///< Propagator to handle the theory constraints
};

}  // namespace dlinear
