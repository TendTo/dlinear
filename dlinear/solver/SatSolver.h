//
// Created by c3054737 on 11/01/24.
//
#pragma once

#include <map>
#include <optional>
#include <set>
#include <vector>

#include "dlinear/symbolic/PlaistedGreenbaumCnfizer.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/ScopedUnorderedMap.hpp"
#include "dlinear/util/ScopedUnorderedSet.hpp"

namespace dlinear {

class SatSolver {
 public:
  explicit SatSolver(const Config &config = Config{});
  virtual ~SatSolver() = default;

  void Pop();
  void Push();
  /**
   * Add a formula @p f to the solver.
   * @note If @p f is a clause, please use @link AddClause function. This
   * function does not assume anything about @p f and perform
   * pre-processings (CNFize and PredicateAbstraction).
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
   * Given a clause = {f₁, ..., fₙ}, adds a clause (¬f₁ ∨ ... ∨ ¬ fₙ) to
   * the solver.
   *
   * @param literals literals to add as the inverted clause
   */
  virtual void AddLearnedClause(const LiteralSet &literals) = 0;
  /**
   * Check the satisfiability of the current configuration.
   *
   * @return a witness, satisfying model if the problem is SAT.
   * @return empty optional if UNSAT
   */
  virtual std::optional<Model> CheckSat() = 0;
  /**
   * Get a theory literal corresponding to the variable @p var.
   *
   * @param var variable that is mapped to a theory literal
   * @return theory literal corresponding to @p var
   */
  Formula theory_literal(const Variable &var) const { return predicate_abstractor_[var]; }

  /**
   * Get all the theory literals the predicate abstractor has converted to a boolean variable.
   * The map allows to retrieve the original theory literal from the boolean variable.
   *
   * @return map between boolean variables and the corresponding theory literals
   */
  const VarToTheoryLiteralMap &var_to_theory_literals() const;

 protected:
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
   * Add a clause @p f to the internal SAT solver.
   * @p f must be a clause. That is, it is either a literal (b or ¬b)
   * or a disjunction of literals (l₁ ∨ ... ∨ lₙ).
   *
   * @param f clause to add
   */
  virtual void AddClauseToSat(const Formula &f) = 0;
  /**
   * Add a variable to the internal SAT solver.
   * Also update the two mapping between each symbolic Variable and the
   * internal SAT solver's variable (@ref var_to_sat_) and the other way around
   * (@ref sat_to_var_).
   * If the variable had already been mapped, this function does nothing.
   *
   * @param var variable to add
   */
  virtual void MakeSatVar(const Variable &var) = 0;
  // Add a symbolic formula @p f.
  //
  // @pre @p f is either a Boolean variable or a negation of Boolean
  // variable.
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
  virtual std::set<int> GetMainActiveLiterals() const = 0;
  /**
   * Get a set of the currently active literals in the clauses,
   * ignoring those required by learned clauses.
   * Here literals are expressed as integers, where the sign indicates
   * whether the literal is negated or not.
   * This method is called from @ref GetMainActiveLiterals.
   * The set of literals is updated by reference.
   *
   * @param lits[out] set of literals
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
   * Update data structures used to remove literals that are only required by
   * learned clauses.
   *
   * @param lit literal from the SAT solver
   * @param learned whether the literal is learned or was in the original
   * formula
   */
  void UpdateLookup(int lit, int learned);

  // Data to help with removing literals that are only required by learned
  // clauses.
  std::vector<int> main_clauses_copy_;
  std::map<int, std::set<size_t>> main_clause_lookup_;
  std::set<int> learned_clause_lits_;
  size_t cur_clause_start_;

  ScopedUnorderedMap<Variable::Id, int> var_to_sat_;  ///< Map symbolic::Variable → int (Variable type in PicoSat).
  ScopedUnorderedMap<int, Variable> sat_to_var_;      ///< Map int (Variable type in PicoSat) → symbolic::Variable.

  PlaistedGreenbaumCnfizer cnfizer_;  ///< CNF converter. Converts the formula to CNF.
  PredicateAbstractor
      predicate_abstractor_;  //< Predicate abstractor. Converts the theory literals to boolean variables.

  ScopedUnorderedSet<Variable::Id>
      cnf_variables_;  ///< Set of temporary Boolean variables introduced by CNF transformations.
};

}  // namespace dlinear
