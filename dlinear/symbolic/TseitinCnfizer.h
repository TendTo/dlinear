/**
 * @file TseitinCnfizer.h
 * @author dlinear
 * @date 19 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */
#pragma once

#include <algorithm>
#include <atomic>
#include <iostream>
#include <iterator>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

#include "dlinear/symbolic/FormulaVisitor.h"
#include "dlinear/symbolic/NaiveCnfizer.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

/**
 * Tsietin transformation is a method to convert a formula into an
 * equi-satisfiable formula in CNF. The method introduces extra Boolean
 * variables (Tseitin transformation).
 */
class TseitinCnfizer : public FormulaVisitor {
 public:
  explicit TseitinCnfizer(const Config &config) : FormulaVisitor{"TseitinCnfizer", config} {}

  /**
   * Convert @p f into an equi-satisfiable formula @c f' in CNF.
   * @param f formula to convert
   * @return equi-satisfiable formula in CNF
   */
  std::vector<Formula> Convert(const Formula &f);

  /**
   * Return a const reference of `map_` member.
   * @note map_ is cleared at the beginning of `Convert` call.
   * @return const reference of `map_` member.n
   */
  const std::map<Variable, Formula> &map() const { return map_; }

 private:
  Formula Visit(const Formula &f) override;
  Formula VisitConjunction(const Formula &f) override;
  Formula VisitDisjunction(const Formula &f) override;
  Formula VisitNegation(const Formula &f) override;
  Formula VisitForall(const Formula &f) override;

  /**
   * Map a temporary variable, which is introduced by a Tseitin
   * transformation, to a corresponding Formula.
   *
   * @note that this map_ is cleared at the beginning of `Convert`
   * call.
   */
  std::map<Variable, Formula> map_;

  const NaiveCnfizer naive_cnfizer_{};  ///< Naive CNFizer. Transforms nested formulas inside universal quantification.

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula, TseitinCnfizer>(TseitinCnfizer *, const Formula &);
};

}  // namespace dlinear
