/**
 * @file CadicalSatSolver.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief SAT solver based on CaDiCal.
 *
 * CaDiCal is a SAT solver written in C++. It is used as a library in dlinear.
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

class CadicalSatSolver : public SatSolver {
 public:
  using SatSolver::FixedTheoryLiterals;
  using SatSolver::Assume;

  explicit CadicalSatSolver(PredicateAbstractor &predicate_abstractor,
                            const std::string &class_name = "CadicalSatSolver");

  void AddLiteral(const Literal &l, bool learned) override;

  void AddLearnedClause(const LiteralSet &literals) override;

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

  CaDiCaL::Solver sat_{};
  int next_var_id_{1};
};

}  // namespace dlinear
