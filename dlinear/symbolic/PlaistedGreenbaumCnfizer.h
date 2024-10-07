/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * PlaistedGreenbaumCnfizer class.
 */
#pragma once

#include <vector>

#include "dlinear/symbolic/FormulaVisitor.h"
#include "dlinear/symbolic/NaiveCnfizer.h"
#include "dlinear/symbolic/Nnfizer.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"

namespace dlinear {

/**
 * Plaisted-Greenbaum transformation is a method to convert a formula into an equi-satisfiable vector of formulae in
 * CNF.
 *
 * The method can introduce extra Boolean variables.
 * Check [Wikipedia](https://en.wikipedia.org/wiki/Plaisted-Greenbaum_transformation) for more information.
 */
class PlaistedGreenbaumCnfizer : public FormulaVisitor {
 public:
  /**
   * Construct a new PlaistedGreenbaumCnfizer object with the given @p config.
   * @param config configuration
   */
  explicit PlaistedGreenbaumCnfizer(const Config &config)
      : FormulaVisitor{config, "PlaistedGreenbaumCnfizer"}, nnfizer_{config}, naive_cnfizer_{config} {}

  /**
   * Convert a @p f into an equi-satisfiable formula @c f' in CNF.
   * @param f A formula to be converted.
   * @return A vector of clauses.
   */
  std::vector<Formula> Convert(const Formula &f);

  /** @getter{auxiliary variables introduced during the conversion, PlaistedGreenbaumCnfizer} */
  [[nodiscard]] const std::vector<Variable> &vars() const { return vars_; }

 private:
  Formula VisitConjunction(const Formula &f) override;
  Formula VisitDisjunction(const Formula &f) override;
  Formula VisitNegation(const Formula &f) override;
  Formula VisitForall(const Formula &f) override;
  const Nnfizer nnfizer_;

  NaiveCnfizer naive_cnfizer_;  ///< Naive CNFizer. Used to transform nested formulas inside universal quantification.

  std::vector<Formula>
      aux_;  ///< Auxiliary clauses collected during conversion. @note It is cleared at the beginning of `Convert` call.

  std::vector<Variable>
      vars_;  ///< Variables generated during conversion. @note It is cleared at the beginning of `Convert` call.
};

}  // namespace dlinear
