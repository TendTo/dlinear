/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "BoundImplicator.h"

#include <ranges>

#include "dlinear/util/exception.h"

namespace dlinear {

BoundImplicator::BoundImplicator(const Config& config, std::function<void(const Formula&)> assert,
                                 const PredicateAbstractor& predicate_abstractor)
    : config_{config}, assert_{std::move(assert)}, predicate_abstractor_{predicate_abstractor} {}

template <>
void BoundImplicator::AddAssertion<1>(const Formula& assertion) {
  DLINEAR_ASSERT(assertion.GetFreeVariables().size() == 1u, "Assertion must have exactly one free variable");
  DLINEAR_ASSERT(is_relational(assertion), "Assertion must be relational");
  const Expression& lhs = get_lhs_expression(assertion);
  const Expression& rhs = get_rhs_expression(assertion);
  DLINEAR_ASSERT((is_variable(lhs) || is_multiplication(lhs)) && is_constant(rhs),
                 "lhs must be a variable or multiplication and rhs must be a constant");

  const mpq_class& constant = get_constant_value(rhs);
  const LpRowSense row_sense = parseLpSense(assertion);
  const Variable* bool_var = &predicate_abstractor_[assertion];

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

void BoundImplicator::Propagate() {
  DLINEAR_ASSERT(config_.actual_bound_implication_frequency() != Config::PreprocessingRunningFrequency::NEVER,
                 "Method Propagate should not be called with a frequency of NEVER");
  for (const auto& [var, assertion] : predicate_abstractor_.var_to_formula_map()) {
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
  PropagateAssertions();
}

void BoundImplicator::PropagateAssertions() {
  for (const auto& [var, constraints] : constraints_) {
    if (constraints.size() <= 1) continue;
    // Propagate simple < and <= constraints
    // Iterate over the array in order (i.e. [ < = <= ] )
    // Then (<) implies (<=), (<) implies (not =), a smaller constraint implies a greater constraint
    // E.g. x < 1 => x <= 1, x < 1 => not (x = 1), x <= 2 => x < 3, x <= 2 => not (x = 3)
    const Constraint* last_l_constraint = nullptr;
    for (const Constraint& constraint : constraints) {
      const auto& [value, sense, bool_var] = constraint;
      if (sense == LpRowSense::LE || sense == LpRowSense::LT) {
        if (last_l_constraint != nullptr) {
          DLINEAR_TRACE_FMT("BoundImplicator::PropagateAssertions: {} => {}",
                            predicate_abstractor_[*last_l_constraint->variable], predicate_abstractor_[*bool_var]);
          assert_(imply(*last_l_constraint->variable, *bool_var));
        }
        last_l_constraint = &constraint;
        continue;
      }
      DLINEAR_ASSERT(sense == LpRowSense::EQ, "Unexpected sense");
      if (last_l_constraint == nullptr) continue;
      assert_(imply(*last_l_constraint->variable, !(*bool_var)));
      DLINEAR_TRACE_FMT("BoundImplicator::PropagateAssertions: {} => {}",
                        predicate_abstractor_[*last_l_constraint->variable], !predicate_abstractor_[*bool_var]);
    }
    // Propagate simple > and >= constraints
    // Iterate over the array in reverse order (i.e. [ > = >= ] )
    // Then (>) implies (>=), (>) implies (not =), a greater constraint implies a lesser constraint
    // E.g. x > 1 => x >= 1, x > 1 => not (x = 1), x >= 2 => x > 1, x >= 2 => not (x = 1)
    const Constraint* last_g_constraint = nullptr;
    for (const Constraint& constraint : std::views::reverse(constraints)) {
      const auto& [value, sense, bool_var] = constraint;
      if (sense == LpRowSense::LE || sense == LpRowSense::LT) {
        if (last_g_constraint != nullptr) {
          DLINEAR_TRACE_FMT("BoundImplicator::PropagateAssertions: {} => {}",
                            !predicate_abstractor_[*last_g_constraint->variable], !predicate_abstractor_[*bool_var]);
          assert_(imply(!*last_g_constraint->variable, !*bool_var));
        }
        last_g_constraint = &constraint;
        continue;
      }
      DLINEAR_ASSERT(sense == LpRowSense::EQ, "Unexpected sense");
      if (last_g_constraint == nullptr) continue;
      assert_(imply(!*last_g_constraint->variable, !(*bool_var)));
      DLINEAR_TRACE_FMT("BoundImplicator::PropagateAssertions: {} => {}",
                        !predicate_abstractor_[*last_g_constraint->variable], !predicate_abstractor_[*bool_var]);
    }
    // Propagate simple = constraints
    // Iterate over the array and make so two different consecutive = constraints cannot be true at the same time
    // Note that this is not complete, since that would require a quadratic number of assertions
    // E.g. not (x = 1) or not (x = 2), not (x = 2) or not (x = 4)
    const Constraint* last_eq_constraint = nullptr;
    for (const Constraint& constraint : constraints) {
      const auto& [value, sense, bool_var] = constraint;
      if (sense != LpRowSense::EQ) continue;
      if (last_eq_constraint != nullptr) {
        if (value == last_eq_constraint->value) {
          DLINEAR_TRACE_FMT("BoundImplicator::PropagateAssertions: {} <=> {}",
                            predicate_abstractor_[*last_eq_constraint->variable], predicate_abstractor_[*bool_var]);
          assert_(iff(*last_eq_constraint->variable, *bool_var));
        } else {
          assert_(!*last_eq_constraint->variable || !*bool_var);
          DLINEAR_TRACE_FMT("BoundImplicator::PropagateAssertions: {} || {}",
                            predicate_abstractor_[*last_eq_constraint->variable], predicate_abstractor_[*bool_var]);
        }
      }
      last_eq_constraint = &constraint;
    }
  }
}

bool BoundImplicator::Constraint::operator==(const BoundImplicator::Constraint& o) const {
  return value == o.value && row_sense == o.row_sense && variable->equal_to(*o.variable);
}
std::strong_ordering BoundImplicator::Constraint::operator<=>(const BoundImplicator::Constraint& o) const {
  const auto& [value_l, type_l, bool_var_l] = *this;
  const auto& [value_r, type_r, bool_var_r] = o;
  if (value_l < value_r) return std::strong_ordering::less;
  if (value_l > value_r) return std::strong_ordering::greater;
  if (type_l < type_r) return std::strong_ordering::less;
  if (type_l > type_r) return std::strong_ordering::greater;
  if (bool_var_l->less(*bool_var_r)) return std::strong_ordering::less;
  if (bool_var_l->equal_to(*bool_var_r)) return std::strong_ordering::equal;
  return std::strong_ordering::greater;
}

}  // namespace dlinear
