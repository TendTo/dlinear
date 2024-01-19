//
// Created by c3054737 on 17/01/24.
//

#include "DeltaSoplexTheorySolver.h"

#include "dlinear/libs/soplex.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

using soplex::Rational;

DeltaSoplexTheorySolver::DeltaSoplexTheorySolver(PredicateAbstractor &predicate_abstractor, const Config &config)
    : SoplexTheorySolver(predicate_abstractor, config) {}

void DeltaSoplexTheorySolver::AddLiteral(const Literal &lit) {
  const auto &[formulaVar, truth] = lit;
  const auto &var_to_formula_map = predicate_abstractor_.var_to_formula_map();
  const auto it = var_to_formula_map.find(formulaVar);
  // Boolean variable - no need to involve theory solver
  if (it == var_to_formula_map.end()) return;
  const auto it2 = lit_to_theory_row_.find(formulaVar.get_id());
  // Literal is already present
  if (it2 != lit_to_theory_row_.end()) return;

  // Theory formula
  const Formula &formula = it->second;
  // Create the LP solver variables
  for (const Variable &var : formula.GetFreeVariables()) AddVariable(var);

  if (IsEqualTo(formula, truth)) {
    // Just create simple bound in LP
    if (IsSimpleBound(formula)) return;
    spx_sense_.push_back('E');
  } else if (IsGreaterThan(formula, truth) || IsGreaterThanOrEqualTo(formula, truth)) {
    // Just create simple bound in LP
    if (IsSimpleBound(formula)) return;
    spx_sense_.push_back('G');
  } else if (IsLessThan(formula, truth) || IsLessThanOrEqualTo(formula, truth)) {
    // Just create simple bound in LP
    if (IsSimpleBound(formula)) return;
    spx_sense_.push_back('L');
  } else if (IsNotEqualTo(formula, truth)) {
    // Nothing to do, because this constraint is always delta-sat for delta > 0.
    return;
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
  }

  Expression expr{(get_lhs_expression(formula) - get_rhs_expression(formula)).Expand()};
  const int spx_row{spx_.numRowsRational()};
  soplex::DSVectorRational coeffs;
  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == spx_sense_.size() - 1, "spx_row must match spx_sense_.size() - 1");
  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == spx_rhs_.size(), "spx_row must match spx_rhs_.size()");
  spx_rhs_.emplace_back(0);
  if (is_constant(expr)) {
    spx_rhs_.back() = -get_constant_value(expr);
  } else if (is_variable(expr)) {
    SetSPXVarCoeff(coeffs, get_variable(expr), 1);
  } else if (is_multiplication(expr)) {
    std::map<Expression, Expression> map = get_base_to_exponent_map_in_multiplication(expr);
    if (map.size() != 1 || !is_variable(map.begin()->first) || !is_constant(map.begin()->second) ||
        get_constant_value(map.begin()->second) != 1) {
      DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", expr);
    }
    SetSPXVarCoeff(coeffs, get_variable(map.begin()->first), get_constant_in_multiplication(expr));
  } else if (is_addition(expr)) {
    const std::map<Expression, mpq_class> &map = get_expr_to_coeff_map_in_addition(expr);
    for (const auto &pair : map) {
      if (!is_variable(pair.first)) {
        DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", expr);
      }
      SetSPXVarCoeff(coeffs, get_variable(pair.first), pair.second);
    }
    spx_rhs_.back() = -get_constant_in_addition(expr);
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", expr);
  }
  if (spx_rhs_.back() <= -soplex::infinity || spx_rhs_.back() >= soplex::infinity) {
    DLINEAR_RUNTIME_ERROR_FMT("LP RHS value too large: {}", spx_rhs_.back());
  }

  // Add inactive constraint
  spx_.addRowRational(soplex::LPRowRational(-soplex::infinity, coeffs, soplex::infinity));
  if (2 == simplex_sat_phase_) CreateArtificials(spx_row);

  // Update indexes
  lit_to_theory_row_.emplace(formulaVar.get_id(), std::tuple(truth, spx_row, -1));
  DLINEAR_ASSERT(static_cast<size_t>(spx_row) == theory_row_to_lit_.size(), "spx_row must match from_spx_row_.size()");
  theory_row_to_lit_.emplace_back(formulaVar, truth);
  DLINEAR_DEBUG_FMT("SoplexSatSolver::AddLinearLiteral({}{} ↦ {})", truth ? "" : "¬", it->second, spx_row);
}

void DeltaSoplexTheorySolver::EnableLiteral(const Literal &lit) {
  const Variable &var = lit.first;
  const bool truth = lit.second;

  const auto it_row = lit_to_theory_row_.find(var.get_id());
  if (it_row != lit_to_theory_row_.end()) {
    // A non-trivial linear literal from the input problem
    const auto &[stored_truth, spx_row, spx_row2] = it_row->second;

    if (stored_truth == truth) {
      const char sense = spx_sense_[spx_row];
      const mpq_class &rhs{spx_rhs_[spx_row]};
      spx_.changeRangeRational(
          spx_row, sense == 'G' || sense == 'E' ? Rational(gmp::to_mpq_t(rhs)) : Rational(-soplex::infinity),
          sense == 'L' || sense == 'E' ? Rational(gmp::to_mpq_t(rhs)) : Rational(soplex::infinity));
      DLINEAR_TRACE_FMT("SoplexSatSolver::EnableLinearLiteral({})", spx_row);
      return;
    }
  }

  // If the literal was not already among the constraints (rows) of the LP, it must be a bound
  // on a variable (column), a learned literal, or a not-equal literal from the
  // input problem (if delta > 0).
  const auto it = predicate_abstractor_.var_to_formula_map().find(var);
  // The variable is not in the map (it is not a theory literal) or it is not a simple bound
  if (it == predicate_abstractor_.var_to_formula_map().end() || !IsSimpleBound(it->second)) {
    DLINEAR_TRACE_FMT("SoplexSatSolver::EnableLinearLiteral: ignoring ({}, {})", var, truth);
    return;
  }

  // A simple bound - set it directly
  const Formula &formula{it->second};
  const Expression &lhs{get_lhs_expression(formula)};
  const Expression &rhs{get_rhs_expression(formula)};
  DLINEAR_TRACE_FMT("SoplexSatSolver::EnableLinearLiteral({}{})", truth ? "" : "¬", formula);
  if (IsEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) {
      SetSPXVarBound(get_variable(lhs), 'B', get_constant_value(rhs));
    } else if (is_constant(lhs) && is_variable(rhs)) {
      SetSPXVarBound(get_variable(rhs), 'B', get_constant_value(lhs));
    } else {
      DLINEAR_UNREACHABLE();
    }
  } else if (IsGreaterThan(formula, truth) || IsGreaterThanOrEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) {
      SetSPXVarBound(get_variable(lhs), 'L', get_constant_value(rhs));
    } else if (is_constant(lhs) && is_variable(rhs)) {
      SetSPXVarBound(get_variable(rhs), 'U', get_constant_value(lhs));
    } else {
      DLINEAR_UNREACHABLE();
    }
  } else if (IsLessThan(formula, truth) || IsLessThanOrEqualTo(formula, truth)) {
    if (is_variable(lhs) && is_constant(rhs)) {
      SetSPXVarBound(get_variable(lhs), 'U', get_constant_value(rhs));
    } else if (is_constant(lhs) && is_variable(rhs)) {
      SetSPXVarBound(get_variable(rhs), 'L', get_constant_value(lhs));
    } else {
      DLINEAR_UNREACHABLE();
    }
  } else if (IsNotEqualTo(formula, truth)) {
    // If delta > 0, we can ignore not-equal bounds on variables, for they will always be satisfied.
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
  }
}

}  // namespace dlinear