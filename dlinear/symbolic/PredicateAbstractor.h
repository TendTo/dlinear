/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * PredicateAbstractor class.
 */
#pragma once

#include <unordered_map>
#include <vector>

#include "dlinear/symbolic/FormulaVisitor.h"
#include "dlinear/symbolic/LinearFormulaFlattener.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"

namespace dlinear {

/**
 * Predicate abstraction is a method to convert a first-order logic formula into a Boolean formula.
 *
 * The boolean formula will be a boolean variable or a conjunction of boolean variables.
 * The object keeps a bijective map between newly introduced the boolean variables and the first-order logic formulae.
 */
class PredicateAbstractor : public FormulaVisitor {
 public:
  /**
   * Construct a new PredicateAbstractor object with the given @p config.
   * @param config configuration
   */
  explicit PredicateAbstractor(const Config &config)
      : FormulaVisitor{config, "PredicateAbstractor"}, flattener_{config} {}
  /**
   * Convert a first-order logic formula @p f into a Boolean formula by predicate abstraction.
   *
   * For example, a formula @f$ (x > 0) \land (y < 0) @f$ will be converted into @f$ b_1 \land b_2 @f$
   * while @f$ b_1 @f$ corresponds with @f$ x > 0 @f$ and  @f$ b_2 @f$ corresponds with @f$ y < 0 @f$.
   * The class provides `operator[b]` which looks up the corresponding formula for a Boolean variable @f$ b @f$.
   * @param f formula to be converted
   * @return boolean formula
   */
  Formula Convert(const Formula &f);

  /**
   * Convert a vector first-order logic formula @p formulas into a Boolean formula
   * by creating a single conjunction through predicate abstraction.
   *
   * For example, a formula @f$ (x > 0) \land (y < 0) @f$ will be converted into @f$ b_1 \land b_2 @f$
   * while @f$ b_1 @f$ corresponds with @f$ x > 0 @f$ and  @f$ b_2 @f$ corresponds with @f$ y < 0 @f$.
   * The class provides `operator[b]` which looks up the corresponding formula for a Boolean variable @f$ b @f$.
   * @param f formula to be converted
   * @return boolean formula
   */
  Formula Convert(const std::vector<Formula> &formulas);

  /** @getter{map of previously converted formulae to variable, PredicateAbstractor} */
  const std::unordered_map<Variable, Formula> &var_to_formula_map() const { return var_to_formula_map_; }

  const Variable &operator[](const Formula &f) const { return formula_to_var_map_.at(f); }
  const Formula &operator[](const Variable &var) const { return var_to_formula_map_.at(var); }

 private:
  /**
   * Visit an atomic formula.
   *
   * It flattens the formula and creates a new Boolean variable if the formula is not present in the map.
   * Otherwise, it returns the corresponding Boolean variable.
   * @param f atomic formula to visit
   * @return newly created Boolean variable in the map @ref var_to_formula_map_ if the formula is not present
   * @return existing Boolean variable in the map @ref var_to_formula_map_ if the formula was already present
   */
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

  std::unordered_map<Variable, Formula>
      var_to_formula_map_;  ///< Map from Boolean variable to previously converted formula.
  std::unordered_map<Formula, Variable>
      formula_to_var_map_;            ///< Map from previously converted formula to Boolean variable.
  LinearFormulaFlattener flattener_;  ///< Linear formula flattener.
};

}  // namespace dlinear
