/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Symbolic utils for testing.
 */
#pragma once

#ifdef DLINEAR_ENABLED_QSOPT_EX
#include "dlinear/libs/libqsopt_ex.h"
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
#include "dlinear/libs/libsoplex.h"
#endif
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/symbolic/symbolic_expression.h"
#include "dlinear/symbolic/symbolic_formula.h"
#include "dlinear/symbolic/symbolic_variable.h"
#include "dlinear/util/Config.h"

using dlinear::Config;
using dlinear::drake::symbolic::Environment;
using dlinear::drake::symbolic::Expression;
using dlinear::drake::symbolic::Formula;
using dlinear::drake::symbolic::FormulaKind;
using dlinear::drake::symbolic::Variable;
using dlinear::drake::symbolic::Variables;
using dlinear::drake::symbolic::VisitExpression;
using dlinear::drake::symbolic::VisitFormula;

inline bool VarEqual(const Variable &v1, const Variable &v2) { return v1.equal_to(v2); }

inline bool VarNotEqual(const Variable &v1, const Variable &v2) { return !VarEqual(v1, v2); }

inline bool VarLess(const Variable &v1, const Variable &v2) { return v1.less(v2); }

inline bool VarNotLess(const Variable &v1, const Variable &v2) { return !VarLess(v1, v2); }

inline bool ExprEqual(const Expression &e1, const Expression &e2) { return e1.EqualTo(e2); }

inline bool ExprNotEqual(const Expression &e1, const Expression &e2) { return !ExprEqual(e1, e2); }

inline bool ExprLess(const Expression &e1, const Expression &e2) { return e1.Less(e2); }

inline bool ExprNotLess(const Expression &e1, const Expression &e2) { return !ExprLess(e1, e2); }

template <typename F>
bool all_of(const std::vector<Formula> &formulas, const F &f) {
  return std::all_of(formulas.begin(), formulas.end(), f);
}

template <typename F>
bool any_of(const std::vector<Formula> &formulas, const F &f) {
  return std::any_of(formulas.begin(), formulas.end(), f);
}

inline bool FormulaEqual(const Formula &f1, const Formula &f2) { return f1.EqualTo(f2); }

inline bool FormulaNotEqual(const Formula &f1, const Formula &f2) { return !FormulaEqual(f1, f2); }

inline bool FormulaLess(const Formula &f1, const Formula &f2) { return f1.Less(f2); }

inline bool FormulaNotLess(const Formula &f1, const Formula &f2) { return !FormulaLess(f1, f2); }
