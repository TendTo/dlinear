/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * TseininCnfizer class.
 */
#pragma once

#include <map>
#include <vector>

#include "dlinear/symbolic/FormulaVisitor.h"
#include "dlinear/symbolic/NaiveCnfizer.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"

namespace dlinear {

/**
 * Tsietin transformation is a method to convert a formula into an equi-satisfiable vector of formulae in CNF.
 *
 * The method can introduce extra Boolean variables.
 * Check [Wikipedia](https://en.wikipedia.org/wiki/Tseytin_transformation) for more information.
 */
class TseitinCnfizer : public FormulaVisitor {
 public:
  /**
   * Construct a new TseitinCnfizer object with the given @p config.
   * @param config configuration
   */
  explicit TseitinCnfizer(const Config &config) : FormulaVisitor{config, "TseitinCnfizer"} {}

  /**
   * Convert @p f into an equi-satisfiable formula in CNF.
   * @param f formula to convert
   * @return vector of equi-satisfiable formulae in CNF
   */
  std::vector<Formula> Convert(const Formula &f);

  /**
   * @getter{map of temporary variables, TseitinCnfizer, @note @ref map_ is cleared at the beginning of @ref Convert }
   */
  [[nodiscard]] const std::map<Variable, Formula> &map() const { return map_; }

 private:
  Formula Visit(const Formula &f) override;
  Formula VisitConjunction(const Formula &f) override;
  Formula VisitDisjunction(const Formula &f) override;
  Formula VisitNegation(const Formula &f) override;
  Formula VisitForall(const Formula &f) override;

  /**
   * Map a temporary variable, which is introduced by a Tseitin transformation, to a corresponding Formula.
   * @note that this map_ is cleared at the beginning of @ref Convert call.
   */
  std::map<Variable, Formula> map_;

  const NaiveCnfizer naive_cnfizer_{};  ///< Naive CNFizer. Transforms nested formulas inside universal quantification.

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula, TseitinCnfizer>(TseitinCnfizer *, const Formula &);
};

}  // namespace dlinear
