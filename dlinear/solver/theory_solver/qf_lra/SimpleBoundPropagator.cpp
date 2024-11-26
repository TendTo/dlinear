/**
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "SimpleBoundPropagator.h"

#include <ranges>

#include "dlinear/util/error.h"

namespace dlinear {

SimpleBoundPropagator::SimpleBoundPropagator(const TheorySolver& theory_solver, const std::string& class_name)
    : TheoryPropagator{theory_solver, class_name} {}

Config::ExecutionStep SimpleBoundPropagator::run_on_step() const {
  return theory_solver().config().actual_simple_bound_propagation_step();
}

template <>
void SimpleBoundPropagator::AddAssertion<1>(const Formula& assertion) {
  DLINEAR_ASSERT(assertion.GetFreeVariables().size() == 1u, "Assertion must have exactly one free variable");
  DLINEAR_ASSERT(is_relational(assertion), "Assertion must be relational");
  const Expression& lhs = get_lhs_expression(assertion);
  const Expression& rhs = get_rhs_expression(assertion);
  DLINEAR_ASSERT((is_variable(lhs) || is_multiplication(lhs)) && is_constant(rhs),
                 "lhs must be a variable or multiplication and rhs must be a constant");

  const mpq_class& constant = get_constant_value(rhs);
  const LpRowSense row_sense = parseLpSense(assertion);
  const Variable bool_var = theory_solver_.predicate_abstractor()[assertion];

  if (row_sense == LpRowSense::NQ) return;  // It is pointless to add nq constraints

  if (is_variable(lhs)) {
    const Variable& var = get_variable(lhs);
    constraints_[var].emplace(constant, row_sense, bool_var);
  } else {
    DLINEAR_ASSERT(is_multiplication(lhs), "lhs must be a multiplication");
    const auto& base_to_exponent_map = get_base_to_exponent_map_in_multiplication(lhs);
    DLINEAR_ASSERT(base_to_exponent_map.size() == 1, "lhs must have exactly one base");
    DLINEAR_ASSERT(is_variable(base_to_exponent_map.begin()->first), "lhs' base must be a variable");
    const Variable& var = get_variable(base_to_exponent_map.begin()->first);
    DLINEAR_ASSERT(is_variable(var), "lhs base must be a variable");
    const mpq_class& coeff = get_constant_in_multiplication(lhs);
    constraints_[var].emplace(constant / coeff, row_sense, bool_var);
  }
}

void SimpleBoundPropagator::PropagateCore(const AssertCallback& assert_cb) {
  for (const auto& [var, assertion] : theory_solver_.predicate_abstractor().var_to_formula_map()) {
    if (!is_relational(assertion)) {
      fmt::println("Assertion must be relational. Skipping.");
      continue;
    }
    switch (assertion.GetFreeVariables().size()) {
      case 1: {
        AddAssertion<1>(assertion);
        break;
      }
      default:
        break;
    }
  }
  PropagateAssertions(assert_cb);
}

void SimpleBoundPropagator::PropagateAssertions(const AssertCallback& assert_cb) {
  const PredicateAbstractor& pa = theory_solver_.predicate_abstractor();
  for (const auto& [var, constraints] : constraints_) {
    if (constraints.size() <= 1) continue;
    // Propagate simple < and <= constraints
    // Iterate over the array in order (i.e. [ < = <= ] )
    // Then (<) implies (<=), (<) implies (not =), a smaller BoundConstraint implies a greater BoundConstraint
    // E.g. x < 1 => x <= 1, x < 1 => not (x = 1), x <= 2 => x < 3, x <= 2 => not (x = 3)
    const BoundConstraint* last_l_constraint = nullptr;
    for (const BoundConstraint& boundConstraint : constraints) {
      const auto& [value, sense, bool_var] = boundConstraint;
      if (sense == LpRowSense::LE || sense == LpRowSense::LT) {
        if (last_l_constraint != nullptr) {
          DLINEAR_DEV_TRACE_FMT("SimpleBoundPropagator::PropagateAssertions: {} => {}", pa[last_l_constraint->variable],
                                pa[bool_var]);
          assert_cb(imply(last_l_constraint->variable, bool_var));
        }
        last_l_constraint = &boundConstraint;
        continue;
      }
      DLINEAR_ASSERT(sense == LpRowSense::EQ, "Unexpected sense");
      if (last_l_constraint == nullptr) continue;
      assert_cb(imply(last_l_constraint->variable, !bool_var));
      DLINEAR_DEV_TRACE_FMT("SimpleBoundPropagator::PropagateAssertions: {} => {}", pa[last_l_constraint->variable],
                            !pa[bool_var]);
    }
    // Propagate simple > and >= constraints
    // Iterate over the array in reverse order (i.e. [ > = >= ] )
    // Then (>) implies (>=), (>) implies (not =), a greater BoundConstraint implies a lesser BoundConstraint
    // E.g. x > 1 => x >= 1, x > 1 => not (x = 1), x >= 2 => x > 1, x >= 2 => not (x = 1)
    const BoundConstraint* last_g_constraint = nullptr;
    for (const BoundConstraint& boundConstraint : std::views::reverse(constraints)) {
      const auto& [value, sense, bool_var] = boundConstraint;
      if (sense == LpRowSense::LE || sense == LpRowSense::LT) {
        if (last_g_constraint != nullptr) {
          DLINEAR_DEV_TRACE_FMT("SimpleBoundPropagator::PropagateAssertions: {} => {}",
                                !pa[last_g_constraint->variable], !pa[bool_var]);
          assert_cb(imply(!last_g_constraint->variable, !bool_var));
        }
        last_g_constraint = &boundConstraint;
        continue;
      }
      DLINEAR_ASSERT(sense == LpRowSense::EQ, "Unexpected sense");
      if (last_g_constraint == nullptr) continue;
      assert_cb(imply(!last_g_constraint->variable, !bool_var));
      DLINEAR_DEV_TRACE_FMT("SimpleBoundPropagator::PropagateAssertions: {} => {}", !pa[last_g_constraint->variable],
                            !pa[bool_var]);
    }
    // Propagate simple = constraints
    // Iterate over the array and make so two different consecutive = constraints cannot be true at the same time
    // Note that this is not complete, since that would require a quadratic number of assertions
    // E.g. not (x = 1) or not (x = 2), not (x = 2) or not (x = 4)
    const BoundConstraint* last_eq_constraint = nullptr;
    for (const BoundConstraint& boundConstraint : constraints) {
      const auto& [value, sense, bool_var] = boundConstraint;
      if (sense != LpRowSense::EQ) continue;
      if (last_eq_constraint != nullptr) {
        if (value == last_eq_constraint->value) {
          DLINEAR_DEV_TRACE_FMT("SimpleBoundPropagator::PropagateAssertions: {} <=> {}",
                                pa[last_eq_constraint->variable], pa[bool_var]);
          assert_cb(iff(last_eq_constraint->variable, bool_var));
        } else {
          assert_cb(!last_eq_constraint->variable || !bool_var);
          DLINEAR_DEV_TRACE_FMT("SimpleBoundPropagator::PropagateAssertions: {} <!=!> {}",
                                pa[last_eq_constraint->variable], pa[bool_var]);
        }
      }
      last_eq_constraint = &boundConstraint;
    }
  }
}

bool SimpleBoundPropagator::BoundConstraint::operator==(const SimpleBoundPropagator::BoundConstraint& o) const {
  return value == o.value && row_sense == o.row_sense && variable.equal_to(o.variable);
}
std::strong_ordering SimpleBoundPropagator::BoundConstraint::operator<=>(
    const SimpleBoundPropagator::BoundConstraint& o) const {
  const auto& [value_l, type_l, bool_var_l] = *this;
  const auto& [value_r, type_r, bool_var_r] = o;
  if (value_l < value_r) return std::strong_ordering::less;
  if (value_l > value_r) return std::strong_ordering::greater;
  if (type_l < type_r) return std::strong_ordering::less;
  if (type_l > type_r) return std::strong_ordering::greater;
  if (bool_var_l.less(bool_var_r)) return std::strong_ordering::less;
  if (bool_var_l.equal_to(bool_var_r)) return std::strong_ordering::equal;
  return std::strong_ordering::greater;
}

}  // namespace dlinear
