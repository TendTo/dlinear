/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * CadicalSatSolver class.
 */
#pragma once

#ifndef DLINEAR_ENABLED_CADICAL
#error CaDiCaL is not enabled. Please enable it by adding "--//tools:enable_cadical" to the bazel command.
#endif

#include <cadical/cadical.hpp>
#include <optional>
#include <set>
#include <string>

#include "dlinear/solver/SatSolver.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

/**
 * SAT solver based on CaDiCal.
 *
 * CaDiCal is a SAT solver written in C++.
 */
class CadicalSatSolver : public SatSolver {
 public:
  using SatSolver::Assume;
  using SatSolver::FixedTheoryLiterals;

  explicit CadicalSatSolver(PredicateAbstractor &predicate_abstractor,
                            const std::string &class_name = "CadicalSatSolver");

  void AddLiteral(const Literal &l, bool learned) override;

  void AddLearnedClause(const LiteralSet &literals) override;
  void AddLearnedClause(const Literal &lit) override;

  void MakeSatVar(const Variable &var) override;

  std::optional<Model> CheckSat() override;

  void Push() override;
  void Pop() override;

  void FixedTheoryLiterals(LiteralSet &fixed_literals) override;

  void Assume(const Literal &l) override;

 protected:
  void AddClauseToSat(const Formula &f) override;

 private:
  [[nodiscard]] std::set<int> GetMainActiveLiterals() override;

  CaDiCaL::Solver sat_{}; ///< SAT solver
  int next_var_id_{1};   ///< Next variable id
};

}  // namespace dlinear
