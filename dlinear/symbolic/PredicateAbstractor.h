/**
 * @file PredicateAbstractor.h
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */
#pragma once

#include <memory>
#include <set>
#include <sstream>
#include <unordered_map>
#include <vector>

#include "dlinear/symbolic/FormulaVisitor.h"
#include "dlinear/symbolic/LinearFormulaFlattener.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"

namespace dlinear {

class PredicateAbstractor : public FormulaVisitor {
 public:
  explicit PredicateAbstractor(const Config &config)
      : FormulaVisitor{config, "PredicateAbstractor"}, flattener_{config} {}
  /**
   * Convert a first-order logic formula @p f into a Boolean formula
   * by predicate abstraction. For example, a formula `(x > 0) ∧ (y <
   * 0)` will be converted into `b₁ ∧ b₂` while `b₁` corresponds with
   * `x > 0` and `b₂` corresponds with `y < 0`. The class provides
   * `operator[b]` which looks up the corresponding formula for a
   * Boolean variable `b`.
   * @param f formula to be converted.
   * @return boolean formula
   */
  Formula Convert(const Formula &f);

  /**
   * Convert a first-order logic formula @p f into a Boolean formula
   * by predicate abstraction. For example, a formula `(x > 0) ∧ (y <
   * 0)` will be converted into `b₁ ∧ b₂` while `b₁` corresponds with
   * `x > 0` and `b₂` corresponds with `y < 0`. The class provides
   * `operator[b]` which looks up the corresponding formula for a
   * Boolean variable `b`.
   * @param formulas formulas to be converted.
   * @return boolean formula
   */
  Formula Convert(const std::vector<Formula> &formulas);

  const std::unordered_map<Variable, Formula, hash_value<Variable>> &var_to_formula_map() const {
    return var_to_formula_map_;
  }

  const Variable &operator[](const Formula &f) const { return formula_to_var_map_.at(f); }

  const Formula &operator[](const Variable &var) const { return var_to_formula_map_.at(var); }

 private:
  Formula Visit(const Formula &f) override;
  Formula VisitAtomic(const Formula &f);
  Formula VisitEqualTo(const Formula &f) override;
  Formula VisitNotEqualTo(const Formula &f) override;
  Formula VisitGreaterThan(const Formula &f) override;
  Formula VisitGreaterThanOrEqualTo(const Formula &f) override;
  Formula VisitLessThan(const Formula &f) override;
  Formula VisitLessThanOrEqualTo(const Formula &f) override;
  Formula VisitConjunction(const Formula &f) override;
  Formula VisitDisjunction(const Formula &f) override;
  Formula VisitNegation(const Formula &f) override;
  Formula VisitForall(const Formula &f) override;

  void Add(const Variable &var, const Formula &f);

  std::unordered_map<Variable, Formula, hash_value<Variable>> var_to_formula_map_;
  std::unordered_map<Formula, Variable> formula_to_var_map_;
  LinearFormulaFlattener flattener_;

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula, PredicateAbstractor>(PredicateAbstractor *, const Formula &);
};

}  // namespace dlinear
