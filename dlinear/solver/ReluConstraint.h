/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * ReluConstraint class.
 */
#pragma once

#include <optional>

#include "dlinear/solver/PiecewiseLinearConstraint.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

/**
 * A ReLU constraint is a kind of piecewise linear constraint.
 *
 * It is used as an activation function in a Neural Network.
 * The ReLU function is defined as:
 * @f[
 * y = \begin{cases}
 * x & \text{if } x > 0 \\
 * 0 & \text{otherwise}
 * \end{cases}
 * @f]
 */
class ReluConstraint : public PiecewiseLinearConstraint {
 public:
  static const mpq_class zero;  ///< Zero constant all the pointers to the default lower bound will point to

  /**
   * Construct a new Relu Constraint object
   *
   * Given the standard ReLU definition, where @p relu_var is @f$ y @f$ and @p e is @f$ x @f$, we store the following:
   * - `inactive_formula` is the formula @f$ y = 0 @f$
   * - `active_formula` is the formula @f$ y = x @f$
   * - `active_soi` is the sum of infeasibility  @f$ y - x @f$ used if the constraint is active.
   * @param relu_var theory variable @f$ y @f$
   * @param e expression @f$ x @f$
   * @param pa predicate abstractor used to convert the formula to a boolean variable
   */
  ReluConstraint(const Variable& relu_var, const Expression& e, const PredicateAbstractor& pa);
  /**
   * Construct a new Relu Constraint object
   *
   * Given the standard ReLU definition, the three theory variables are:
   * - `inactive_var` is the boolean variable associated with the formula @f$ y = 0 @f$
   * - `active_var` is the boolean variable associated with the formula @f$ y = x @f$
   * - `relu_var` is the theory variable @f$ y @f$
   * @param active_var boolean variable associated with the formula @f$ y = x @f$
   * @param inactive_var boolean variable associated with the formula @f$ y = 0 @f$
   * @param relu_var theory variable @f$ y @f$
   * @param active_soi sum of infeasibility  @f$ y - x @f$ used if the constraint is active.
   * It must be @f$ 0 @f$ for the constraint to be satisfied
   */
  ReluConstraint(Variable active_var, Variable inactive_var, Variable relu_var, Expression active_soi);

  void UpdateUpperBound(const mpq_class* upper_bound) override;
  void UpdateLowerBound(const mpq_class* lower_bound) override;

  void EnableLiteral(const Variable& var);

  std::set<LiteralSet> TightenBounds(BoundPreprocessor& preprocessor) override;

  [[nodiscard]] LiteralSet Assumptions() const override;

  [[nodiscard]] LiteralSet LearnedClauses() const override;

  std::ostream& Print(std::ostream& os) const override;
};

}  // namespace dlinear
