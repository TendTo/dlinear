/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * SatSolver class.
 */
#pragma once

#include <cstddef>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

#include "dlinear/symbolic/PlaistedGreenbaumCnfizer.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/ScopedUnorderedMap.hpp"
#include "dlinear/util/ScopedUnorderedSet.hpp"
#include "dlinear/util/Stats.h"

namespace dlinear {

/**
 * Base class for SAT solvers.
 *
 * The SAT solver's role is to convert a generic formula into a CNF of boolean clauses,
 * abstracting away the theory literals.
 * Then, it checks the satisfiability of the CNF.
 * If the CNF is satisfiable, it returns a model for the formula.
 * Otherwise, it returns an empty optional.
 * The SAT solver can learn clauses during the solving process, guided by the theory solver.
 * @see TheorySolver
 */
class SatSolver {
 public:
  /**
   * Construct a new SatSolver object.
   *
   * The @p predicate_abstractor is shared between the theory solver and the SAT solver, in order to have a common
   * understanding of the literals.
   * The @p class_name is used to identify the theory solver in the logs.
   * @note The @p predicate abstractor will share its configuration with the SAT solver.
   * @param class_name name of the subclass of the SAT solver used
   * @param predicate_abstractor predicate abstractor linking boolean literals to theory literals
   * @see TheorySolver
   */
  explicit SatSolver(PredicateAbstractor &predicate_abstractor, const std::string &class_name = "SatSolver");
  virtual ~SatSolver() = default;

  virtual void Push() = 0;
  virtual void Pop() = 0;
  /**
   * Add a formula @p f to the solver.
   * @note If @p f is a clause, please use @ref AddClause function. This
   * function does not assume anything about @p f and perform
   * pre-processing (CNFize and PredicateAbstraction).
   *
   * @param f formula to add
   */
  void AddFormula(const Formula &f);
  /**
   * Add the @p formulas to the solver.
   *
   * @param formulas vector of formulas to add
   */
  void AddFormulas(const std::vector<Formula> &formulas);
  /**
   * Add a formula @p f to the solver.
   * @p f must be a clause. That is, it is either a literal (b or ¬b)
   * or a disjunction of literals (l₁ ∨ ... ∨ lₙ).
   *
   * @param f formula to add
   */
  void AddClause(const Formula &f);
  /**
   * Add a vector of formulas @p formulas to the solver.
   * Each formula must be a clause. That is, it is either a literal (b or ¬b)
   * or a disjunction of literals (l₁ ∨ ... ∨ lₙ).
   *
   * @param formulas vector of formulas to add
   */
  void AddClauses(const std::vector<Formula> &formulas);
  /**
   * Given a clause = {f₁, ..., fₙ}, adds a clause (¬f₁ ∨ ... ∨ ¬ fₙ) to the solver.
   *
   * @param literals literals to add as the inverted clause
   */
  virtual void AddLearnedClause(const LiteralSet &literals) = 0;
  /**
   * Given a clause = {f}, adds a clause (¬f) to the solver.
   *
   * @param literals literals to add as the inverted clause
   */
  virtual void AddLearnedClause(const Literal &literals) = 0;
  /**
   * Get the theory literals that are fixed in the current configuration.
   *
   * This means that, for the model to be sat, these literals will never change their assignment.
   * This allows for slight optimizations
   * (e.g. their bound can be computed once, at the beginning of the run instead of at each iteration)
   * @return set of literals that are fixed
   */
  LiteralSet FixedTheoryLiterals();
  /**
   * Get the theory literals that are fixed in the current configuration.
   *
   * This means that, for the model to be sat, these literals will never change their assignment.
   * This allows for slight optimizations
   * (e.g. their bound can be computed once, at the beginning of the run instead of at each iteration)
   * @param[out] fixed_literals set of literals that are fixed
   */
  virtual void FixedTheoryLiterals(LiteralSet &fixed_literals) = 0;

  /**
   * Assumption a set of @p literals to be fixed for the next iteration.
   *
   * The @p literals are temporarily added to the solver with the indicated value.
   * @note The solver will not remember the assumptions after the next call to @ref CheckSat.
   * @param literals set of literals to assume
   */
  void Assume(const LiteralSet &literals);
  /**
   * Assumption a literals to be fixed for the next iteration.
   *
   * The @p lit is temporarily added to the solver with the indicated value.
   * @note The solver will not remember the assumption after the next call to @ref CheckSat.
   * @param lit literal to assume
   */
  virtual void Assume(const Literal &lit) = 0;

  /**
   * Mark @p var as a CNF variable.
   *
   * It won't be present in the model produced by the SAT solver.
   * @param var variable to mark
   */
  void MarkAsCnfVariable(const Variable &var);

  /**
   * Check the satisfiability of the current configuration.
   * @return a witness, satisfying model if the problem is SAT.
   * @return empty optional if UNSAT
   */
  virtual std::optional<Model> CheckSat() = 0;
  /** @getter{statistics, SAT solver}*/
  [[nodiscard]] const IterationStats &stats() const { return stats_; }
  /** @getter{statistics of the cnfizer, SAT solver} */
  [[nodiscard]] const IterationStats &cnfizer_stats() const;
  /** @getter{predicate abstractor, SAT solver} */
  [[nodiscard]] const PredicateAbstractor &predicate_abstractor() const { return predicate_abstractor_; }

  [[nodiscard]] std::vector<std::vector<Literal>> clauses() const;

 protected:
  /**
   * Add a clause @p f to the internal SAT solver.
   * @pre @p f must be a clause. That is, it is either a literal (b or ¬b)
   * or a disjunction of literals (l₁ ∨ ... ∨ lₙ).
   * @param f clause to add
   */
  virtual void AddClauseToSat(const Formula &f) = 0;
  /**
   * Add a variable to the internal SAT solver.
   *
   * Also update the two mapping between each symbolic Variable and the
   * internal SAT solver's variable (@ref var_to_sat_) and the other way around
   * (@ref sat_to_var_).
   * If the variable had already been mapped, this function does nothing.
   * @param var variable to add
   */
  virtual void MakeSatVar(const Variable &var) = 0;
  /**
   * Add a formula @p f to the solver.
   * @p f must be a Boolean variable or a negation of Boolean variable (b or ¬b).
   *
   * @param f formula to add
   */
  void AddLiteral(const Formula &f);
  /**
   * Add a literal @p l to the SAT solver.
   * If the literal is @p learned, it is added to the learned clause set
   * and won't be used by the theory solver.
   *
   * @param l literal to add
   * @param learned whether the literal is learned or was in the original
   * formula
   */
  virtual void AddLiteral(const Literal &l, bool learned) = 0;
  /**
   * Get a set of the currently active literals in the clauses,
   * ignoring those required by learned clauses.
   * Here literals are expressed as integers, where the sign indicates
   * whether the literal is negated or not.
   *
   * @return set of literals
   */
  virtual std::set<int> GetMainActiveLiterals() = 0;
  /**
   * Get a set of the currently active literals in the clauses,
   * ignoring those required by learned clauses.
   * Here literals are expressed as integers, where the sign indicates
   * whether the literal is negated or not.
   * This method is called from @ref GetMainActiveLiterals.
   * The set of literals is updated by reference.
   *
   * @param[out] lits set of literals
   */
  void GetMainActiveLiterals(std::set<int> &lits) const;
  /**
   * If the SAT solver returns SAT, this function can be used to obtain a model
   * for the formula.
   *
   * @return model returned by the SAT solver
   */
  Model OnSatResult();
  /**
   * Update data structures used to minimize the number of assigned literals the theory solver has to verify.
   * @param lit literal from the SAT solver
   */
  void UpdateLookup(int lit);

  const Config &config_;  ///< Configuration of the SAT solver

  // Data to help with removing literals that are only required by learned clauses.
  std::vector<int> main_clauses_copy_;  ///< Store the main clauses to restore them after the SAT solver call.
  std::map<int, std::set<std::size_t>> main_clause_lookup_;  ///< Lookup table for literals in the main clauses.
  std::size_t cur_clause_start_;                             ///< Index of the first clause added by the SAT solver.

  ScopedUnorderedMap<Variable::Id, int> var_to_sat_;  ///< Map symbolic::Variable → int (Variable type in PicoSat).
  ScopedUnorderedMap<int, Variable> sat_to_var_;      ///< Map int (Variable type in PicoSat) → symbolic::Variable.
  ScopedUnorderedSet<Variable::Id>
      cnf_variables_;  ///< Set of temporary Boolean variables introduced by CNF transformations.

  PlaistedGreenbaumCnfizer cnfizer_;           ///< Converts the formula to CNF.
  PredicateAbstractor &predicate_abstractor_;  ///< Converts the theory literals to boolean variables.

  IterationStats stats_;  ///< Statistics for the solver.
};

}  // namespace dlinear
