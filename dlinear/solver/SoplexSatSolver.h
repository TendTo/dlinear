/**
 * @file SoplexSatSolver.h
 * @author dlinear
 * @date 24 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */

#ifndef DLINEAR5_DLINEAR_SOLVER_SOPLEXSATSOLVER_H_
#define DLINEAR5_DLINEAR_SOLVER_SOPLEXSATSOLVER_H_

#include <picosat/picosat.h>

#include <memory>
#include <set>
#include <map>
#include <utility>
#include <vector>
#include <unordered_map>
#include <ostream>
#include <cmath>

#include <tl/optional.hpp>

#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/util/ScopedUnorderedMap.hpp"
#include "dlinear/util/ScopedUnorderedSet.hpp"
#include "dlinear/symbolic/PlaistedGreenbaumCnfizer.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/libs/gmp.h"
#include "dlinear/libs/soplex.h"

namespace dlinear {

class SoplexSatSolver {
 public:
  // Boolean model + Theory model.
  /** Boolean model + Theory model. */
  using Model = std::pair<std::vector<Literal>, std::vector<Literal>>;

  /**
   * Construct a SoplexSatSolver.
   * @param config configuration
   */
  explicit SoplexSatSolver(const Config &config);

  /// Constructs a SoplexSatSolver while asserting @p clauses.
  /**
   * Construct a SoplexSatSolver while asserting @p clauses.
   * @param config configuration
   * @param clauses clauses to assert
   */
  SoplexSatSolver(const Config &config, const std::vector<Formula> &clauses);

  SoplexSatSolver(const SoplexSatSolver &) = delete;
  SoplexSatSolver(SoplexSatSolver &&) = delete;
  SoplexSatSolver &operator=(const SoplexSatSolver &) = delete;
  SoplexSatSolver &operator=(SoplexSatSolver &&) = delete;

  ~SoplexSatSolver();

  /**
   * Add a formula @p f to the solver.
   *
   * @note If @p f is a clause, please use AddClause function. This
   * function does not assume anything about @p f and perform
   * pre-processings (CNFize and PredicateAbstraction).
   * @param f formula to add
   */
  void AddFormula(const Formula &f);

  /**
   * Add a vector of formulas @p formulas to the solver.
   * @param formulas vector of formulas to add
   */
  void AddFormulas(const std::vector<Formula> &formulas);

  /**
   * Given a @p formulas = {f₁, ..., fₙ}, adds a clause (¬f₁ ∨ ... ∨ ¬ fₙ) to
   * the solver.
   * @param literals literals contained in the new clause
   */
  void AddLearnedClause(const LiteralSet &literals);

  /**
   * Check the satisfiability of the current configuration
   * @param box box of variables to check
   * @return whether the problem is satisfiable as an optional
   */
  tl::optional <Model> CheckSat(const Box &box);

  // TODO(soonho): Push/Pop cnfizer and predicate_abstractor?
  void Pop();

  void Push();

  Formula theory_literal(const Variable &var) const {
    return predicate_abstractor_[var];
  }

  soplex::SoPlex *GetLinearSolverPtr() {
    return &spx_prob_;
  }

  const soplex::VectorRational &GetLowerBounds() const {
    return spx_lower_;
  }

  const soplex::VectorRational &GetUpperBounds() const {
    return spx_upper_;
  }

  const std::map<int, Variable> &GetLinearVarMap() const;

 private:
  /**
   * Add a clause @p f to the solver.
   * @pre @p f is a clause. That is, it is either a literal (b or ¬b)
   * or a disjunction of literals (l₁ ∨ ... ∨ lₙ).
   * @param f clause to add
   */
  void AddClause(const Formula &f);

  /**
   * Add a vector of formulas @p formulas to the solver.
   * @pre Each element of @p formulas must be a clause.
   * @param formulas vector of formulas to add
   */
  void AddClauses(const std::vector<Formula> &formulas);

  /**
   * Return a corresponding literal ID of @p var.
   * It maintains two maps `lit_to_var_` and `var_to_lit_` to keep track of the
   * relationship between Variable ⇔ Literal (in SAT).
   * @param var variable to convert in the corresponding literal
   */
  void MakeSatVar(const Variable &var);

  /**
   * Disable all literals in the linear solver restricting variables to the
   * given @p box only.
   * @param box box of variables to restrict
   */
  void ResetLinearProblem(const Box &box);

  // Add a symbolic formula @p f to @p clause.
  //
  // @pre @p f is either a Boolean variable or a negation of Boolean
  // variable.
  void AddLiteral(const Formula &f);
  void AddLiteral(const Literal &l, bool learned);

  // Add a linear literal to the linear solver
  void AddLinearLiteral(const Variable &var, bool truth);

  // Create (redundant) artificial variable for LP solver
  void CreateArtificials(int spx_row);

  // Enable a linear literal in the linear solver
  void EnableLinearLiteral(const Variable &var, bool truth);

  // Add a variable to the linear solver
  void AddLinearVariable(const Variable &var);

  // Set the variable's coefficient for the given constraint row in the linear
  // solver
  void SetSPXVarCoef(soplex::DSVectorRational *coeffs, const Variable &var,
                     const mpq_class &value);

  // Set one of the variable's bounds ('L' - lower or 'U' - upper) in the
  // linear solver, in addition to bounds already asserted.
  void SetSPXVarBound(const Variable &var, const char type,
                      const mpq_class &value);

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

  // Exact LP solver (SoPlex)
  soplex::SoPlex spx_prob_;
  soplex::VectorRational spx_lower_;
  soplex::VectorRational spx_upper_;

  // Map symbolic::Variable <-> int (column in SoPlex problem).
  // We don't use the scoped version because we'd like to be sure that we
  // won't create duplicate columns.  No two Variable objects ever have the
  // same Id.
  std::map<Variable::Id, int> to_spx_col_;
  std::map<int, Variable> from_spx_col_;

  // Map (symbolic::Variable, bool) <-> int (row in SoPlex problem).
  std::map<std::pair<Variable::Id, bool>, int> to_spx_row_; ///< Map (Variable, bool) <-> int (row)
  std::vector<Literal> from_spx_row_; ///< Map int (row) <-> Literal

  std::vector<mpq_class> spx_rhs_;
  std::vector<char> spx_sense_;

  /// @note We found an issue when picosat_deref_partial is used with
  /// picosat_pop. When this variable is true, we use `picosat_deref`
  /// instead.
  ///
  /// TODO(soonho): Remove this hack when it's not needed.
  bool has_picosat_pop_used_{false};

  const Config &config_; ///< Solver configuration
};

} // namespace dlinear

#endif //DLINEAR5_DLINEAR_SOLVER_SOPLEXSATSOLVER_H_
