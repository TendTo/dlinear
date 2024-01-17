/**
 * @file QsoptexSatSolver.h
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */
#pragma once

#include <picosat/picosat.h>

#include <map>
#include <optional>
#include <set>
#include <utility>
#include <vector>

#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/symbolic/PlaistedGreenbaumCnfizer.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/ScopedUnorderedMap.hpp"
#include "dlinear/util/ScopedUnorderedSet.hpp"

namespace dlinear {

class QsoptexSatSolver {
 public:
  using Model = std::pair<std::vector<Literal>, std::vector<Literal>>;  ///< Boolean model + Theory model.

  /**
   * Construct a QsoptexSatSolver.
   * @param config configuration
   */
  explicit QsoptexSatSolver(const Config &config);

  /**
   * Construct a QsoptexSatSolver while asserting @p clauses.
   * @param config configuration
   * @param clauses clauses to assertla
   */
  QsoptexSatSolver(const Config &config, const std::vector<Formula> &clauses);
  QsoptexSatSolver(const QsoptexSatSolver &) = delete;
  QsoptexSatSolver(QsoptexSatSolver &&) = delete;
  QsoptexSatSolver &operator=(const QsoptexSatSolver &) = delete;
  QsoptexSatSolver &operator=(QsoptexSatSolver &&) = delete;

  ~QsoptexSatSolver();

  /**
   * Add a formula @p f to the solver.
   * @note If @p f is a clause, please use @ref AddClause function. This
   * function does not assume anything about @p f and perform
   * pre-processings (CNFize and PredicateAbstraction).
   * @param f formula to be added
   */
  void AddFormula(const Formula &f);

  /**
   * Add a vector of formulas @p formulas to the solver.
   * @note If @p f is a clause, please use @ref AddClauses function. This
   * @param formulas
   */
  void AddFormulas(const std::vector<Formula> &formulas);

  /**
   * Given a @p formulas = {f₁, ..., fₙ}, adds a clause (¬f₁ ∨ ... ∨ ¬ fₙ) to
   * the solver.
   * @param literals literals contained in the new clause
   */
  void AddLearnedClause(const LiteralSet &literals);

  /**
   * Check the satisfiability of the current configuration.
   * Also set up the linear solver returned by GetLinearSolver().
   * @param box box of variables to check
   * @param obj_expr the objective expression to minimize
   * @return a witness, satisfying model if the problem is satisfiable, nullopt if UNSAT
   */
  std::optional<Model> CheckSat(const Box &box, std::optional<Expression> obj_expr = std::optional<Expression>{});

  // TODO(soonho): Push/Pop cnfizer and predicate_abstractor?
  void Pop();

  void Push();

  Formula theory_literal(const Variable &var) const { return predicate_abstractor_[var]; }

  mpq_QSprob GetLinearSolver() const { return qsx_prob_; }

  const std::map<int, Variable> &GetLinearVarMap() const;

 private:
  /**
   * Add a clause @p f to the solver.
   * @note @p f must be a clause. That is, it is either a literal (b or ¬b)
   * or a disjunction of literals (l₁ ∨ ... ∨ lₙ).
   * @param f clause to be added
   */
  void AddClause(const Formula &f);

  /**
   * Add a vector of formulas @p formulas to the solver.
   * @note Each element of @p formulas must be a clause. That is, it is either
   * a literal (b or ¬b) or a disjunction of literals (l₁ ∨ ... ∨ lₙ).
   *
   * @param formulas set of clauses to be added
   */
  void AddClauses(const std::vector<Formula> &formulas);

  /**
   * Return a corresponding literal ID of @p var.
   * It maintains two maps `lit_to_var_` and `var_to_lit_` to keep track of the
   * relationship between Variable ⇔ Literal (in SAT).
   *
   * @param var variable to add to the SAT solver
   */
  void MakeSatVar(const Variable &var);

  /**
   * Disable all literals in the linear solver restricting variables to the
   * given @p box only.
   *
   * @param box box of variables to restrict
   */
  void ResetLinearProblem(const Box &box);

  /**
   * Add a symbolic formula @p f to @p clause.
   * @pre @p f is either a Boolean variable or a negation of Boolean variable
   *
   * @param f formula to add
   */
  void AddLiteral(const Formula &f);
  void AddLiteral(const Literal &l, bool learned);

  // Add a linear literal to the linear solver
  void AddLinearLiteral(const Variable &var, bool truth);

  // Enable a linear literal in the linear solver
  void EnableLinearLiteral(const Variable &var, bool truth);

  // Add a variable to the linear solver
  void AddLinearVariable(const Variable &var);

  // Clear the linear solver's objective function
  void ClearLinearObjective();

  // Set the linear solver's objective function
  void SetLinearObjective(const Expression &obj_expr);

  // Set the variable's coefficient for the given constraint row in the linear
  // solver
  void SetQSXVarCoef(int qsx_row, const Variable &var, const mpq_class &value);

  // Set the variable's coefficient for the objective function in the linear
  // solver
  void SetQSXVarObjCoef(const Variable &var, const mpq_class &value);

  // Set one of the variable's bounds ('L' - lower or 'U' - upper) in the
  // linear solver, in addition to bounds already asserted.
  void SetQSXVarBound(const Variable &var, const char type, const mpq_class &value);

  // Add a clause @p f to sat solver.
  void DoAddClause(const Formula &f);

  // Update data structures used to remove literals that are only required by
  // learned clauses.
  void UpdateLookup(int lit, int learned);

  // Collect active literals, removing those that are only required by learned
  // clauses.
  std::set<int> GetMainActiveLiterals() const;

  // Member variables
  // ----------------
  // Pointer to the PicoSat solver.
  PicoSAT *const sat_{};
  PlaistedGreenbaumCnfizer cnfizer_;
  PredicateAbstractor predicate_abstractor_;

  // Map symbolic::Variable → int (Variable type in PicoSat).
  ScopedUnorderedMap<Variable::Id, int> to_sat_var_;

  // Map int (Variable type in PicoSat) → symbolic::Variable.
  ScopedUnorderedMap<int, Variable> to_sym_var_;

  // Data to help with removing literals that are only required by learned
  // clauses.
  std::vector<int> main_clauses_copy_;
  std::set<int> learned_clause_lits_;
  std::map<int, std::set<int>> main_clause_lookup_;
  int cur_clause_start_;

  /// Set of temporary Boolean variables introduced by CNF
  /// transformations.
  ScopedUnorderedSet<Variable::Id> cnf_variables_;

  // Exact LP solver (QSopt_ex)
  mpq_QSprob qsx_prob_;

  // Map symbolic::Variable <-> int (column in QSopt_ex problem).
  // We don't use the scoped version because we'd like to be sure that we
  // won't create duplicate columns.  No two Variable objects ever have the
  // same Id.
  std::map<Variable::Id, int> to_qsx_col_;
  std::map<int, Variable> from_qsx_col_;

  // Map (symbolic::Variable, bool) <-> int (row in QSopt_ex problem).
  std::map<std::pair<Variable::Id, bool>, int> to_qsx_row_;
  std::vector<Literal> from_qsx_row_;

  std::vector<mpq_class> qsx_rhs_;
  std::vector<char> qsx_sense_;

  /// @note We found an issue when picosat_deref_partial is used with
  /// picosat_pop. When this variable is true, we use `picosat_deref`
  /// instead.
  ///
  /// TODO(soonho): Remove this hack when it's not needed.
  bool has_picosat_pop_used_{false};

  const Config &config_;
};

}  // namespace dlinear
