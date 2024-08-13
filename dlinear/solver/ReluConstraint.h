/**
 * @file ReluConstraint.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * ReluConstraint class
 */
#pragma once

#include <optional>

#include "dlinear/solver/GuidedConstraint.h"
#include "dlinear/symbolic/PredicateAbstractor.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

class ReluConstraint : public GuidedConstraint {
 public:
  const static mpq_class zero;

  /**
   * Construct a new Relu Constraint object
   *
   * Given a ReLU formula
   * @f[
   * r = \begin{cases}
   * 0 & \text{if } f < 0 \\
   * f & \text{otherwise}
   * \end{cases} @f]
   * the three theory variables are:
   * - `inactive_formula` is the formula @f$ r = 0 @f$
   * - `active_formula` is the boolean variable associated with the formula @f$ r = f @f$
   * - `relu_var` is the theory variable @f$ r @f$
   * @param inactive_formula formula @f$ r = 0 @f$
   * @param active_formula boolean variable associated with the formula @f$ r = f @f$
   * @param relu_var theory variable @f$ r @f$
   * @param pa predicate abstractor used to convert the formula to a boolean variable
   */
  ReluConstraint(const Formula& inactive_formula, const Formula& active_formula, Variable relu_var,
                 const PredicateAbstractor& pa);
  /**
   * Construct a new Relu Constraint object
   *
   * Given a ReLU formula
   * @f[
   * r = \begin{cases}
   * 0 & \text{if } f < 0 \\
   * f & \text{otherwise}
   * \end{cases} @f]
   * the three theory variables are:
   * - `inactive_var` is the boolean variable associated with the formula @f$ r = 0 @f$
   * - `active_var` is the boolean variable associated with the formula @f$ r = f @f$
   * - `relu_var` is the theory variable @f$ r @f$
   * @param inactive_var boolean variable associated with the formula @f$ r = 0 @f$
   * @param active_var boolean variable associated with the formula @f$ r = f @f$
   * @param relu_var theory variable @f$ r @f$
   */
  ReluConstraint(Variable inactive_var, Variable active_var, Variable relu_var);

  void SetBounds(const mpq_class& lower_bound, const mpq_class& upper_bound);
  void SetUpperBound(const mpq_class& upper_bound);
  void SetLowerBound(const mpq_class& lower_bound);
  void SetBounds(const mpq_class* lower_bound, const mpq_class* upper_bound);
  void SetUpperBound(const mpq_class* upper_bound);
  void SetLowerBound(const mpq_class* lower_bound);

  [[nodiscard]] const mpq_class& lower_bound() const { return *lower_bound_; }
  [[nodiscard]] const mpq_class& upper_bound() const { return *upper_bound_; }
  [[nodiscard]] const Variable& inactive_var() const { return inactive_var_; }
  [[nodiscard]] const Variable& active_var() const { return active_var_; }
  [[nodiscard]] const Variable& relu_var() const { return relu_var_; }

  [[nodiscard]] bool fixed() const { return *lower_bound_ > 0 || *upper_bound_ == 0; }

  [[nodiscard]] LiteralSet Assumptions() const override;

  [[nodiscard]] LiteralSet LearnedClauses() const override;

  std::ostream& Print(std::ostream& os) const override;

 private:
  const mpq_class* lower_bound_;
  const mpq_class* upper_bound_;

  const Variable inactive_var_;
  const Variable active_var_;
  const Variable relu_var_;
};

}  // namespace dlinear
