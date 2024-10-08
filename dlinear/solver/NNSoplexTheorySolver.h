/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Theory solver using SoPlex.
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

/**
 * Specialised theory solver for neural networks using SoPlex.
 *
 * The solver will use special care when dealing with piecewise linear constraints.
 * Instead of encoding them as a set of linear constraints, they will create a new objective function
 * representing the sum of infeasibilities to minimise.
 * If the problem is feasible, but the objective value is not 0, the solver will try to invert the greatest
 * violation to attempt making the problem feasible.
 */
class NNSoplexTheorySolver : public SoplexTheorySolver {
 public:
  explicit NNSoplexTheorySolver(PredicateAbstractor &predicate_abstractor,
                                const std::string &class_name = "NNSoplexTheorySolver");

  void SetPiecewiseLinearConstraints(const std::vector<std::unique_ptr<PiecewiseLinearConstraint>> &relu_constraints);

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

  /** Convert the @ref soi_ expression to an objective function inside soplex */
  void SoiToObjFunction();

  /** Invert the greatest violation found in the objective function */
  bool InvertGreatestViolation();

  std::unordered_map<Variable, const PiecewiseLinearConstraint *> pl_theory_lit_;
  std::vector<PlConstraint> enabled_pl_constraints_;
  Explanations pl_explanations_;
  Expression soi_;
};

}  // namespace dlinear
