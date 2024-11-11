/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @copyright 2017 Toyota Research Institute (dreal4)
 * @licence BSD 3-Clause License
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
class TseitinCnfizer : public FormulaVisitor<std::map<Variable, Formula> &> {
 public:
  /**
   * Construct a new TseitinCnfizer object with the given @p config.
   * @param config configuration
   */
  explicit TseitinCnfizer(const Config &config) : FormulaVisitor{config, "TseitinCnfizer"}, naive_cnfizer_{config_} {}

  /**
   * Convert @p f into an equi-satisfiable formula in CNF.
   * @param f formula to convert
   * @return vector of equi-satisfiable formulae in CNF
   */
  [[nodiscard]] std::vector<Formula> Process(const Formula &f) const;
  [[nodiscard]] std::vector<Formula> operator()(const Formula &f) const;

 private:
  [[nodiscard]] Formula VisitConjunction(const Formula &f, std::map<Variable, Formula> &map) const override;
  [[nodiscard]] Formula VisitDisjunction(const Formula &f, std::map<Variable, Formula> &map) const override;
  [[nodiscard]] Formula VisitNegation(const Formula &f, std::map<Variable, Formula> &map) const override;
  [[nodiscard]] Formula VisitForall(const Formula &f, std::map<Variable, Formula> &map) const override;

  const NaiveCnfizer naive_cnfizer_;  ///< Naive CNFizer. Transforms nested formulas inside universal quantification.
};

}  // namespace dlinear
