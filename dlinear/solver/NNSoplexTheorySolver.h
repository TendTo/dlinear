/**
 * @file NNSoplexTheorySolver.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Theory solver using SoPlex.
 *
 * Neural network theory solver using SoPlex.
 */
#pragma once

#include <unordered_set>

#include "dlinear/solver/PiecewiseLinearConstraint.h"
#include "dlinear/solver/SoplexTheorySolver.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

class NNSoplexTheorySolver : public SoplexTheorySolver {
 public:
  explicit NNSoplexTheorySolver(PredicateAbstractor &predicate_abstractor,
                                const std::string &class_name = "NNSoplexTheorySolver");

  void SetPiecewiseLinearConstraints(const std::vector<std::unique_ptr<PiecewiseLinearConstraint>> &relu_constraints) {
    for (const auto &relu_constraint : relu_constraints) {
      pl_theory_lit_.emplace(relu_constraint->active_var(), relu_constraint.get());
      pl_theory_lit_.emplace(relu_constraint->inactive_var(), relu_constraint.get());
      // fmt::println("Adding relu constraint: {} - {}", relu_constraint->active_var(),
      // relu_constraint->inactive_var());
    }
  }

  void AddLiteral(const Variable &formula_var, const Formula &formula) override;
  Explanations EnableLiteral(const Literal &lit) override;
  SatResult CheckSatCore(mpq_class *actual_precision, std::set<LiteralSet> &explanations) override;
  void Reset() override;

 private:
  enum class SpxCheckSatResult {
    SAT,
    SOI_VIOLATION,
    INFEASIBLE,
  };

  struct PlConstraint {
    const PiecewiseLinearConstraint *constraint;
    bool active;
    bool fixed;
  };

  SpxCheckSatResult SpxCheckSat(mpq_class *actual_precision);

  void EnableSpxRow(int spx_row, bool truth) override;

  void Consolidate(const Box &box) override;

  void UpdateExplanationsWithCurrentPiecewiseLinearLiterals(std::set<LiteralSet> &explanations);

  void SoiToObjFunction();

  bool InvertGreatestViolation();

  std::unordered_map<Variable, const PiecewiseLinearConstraint *> pl_theory_lit_;
  std::vector<PlConstraint> enabled_pl_constraints_;
  Explanations pl_explanations_;
  Expression soi_;
};

}  // namespace dlinear
