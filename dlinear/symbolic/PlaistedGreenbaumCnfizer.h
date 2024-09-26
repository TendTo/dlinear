/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
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
 * Plaisted-Greenbaum transformation is a method to convert a formula into an equi-satisfiable vector of formulae in CNF.
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
  explicit PlaistedGreenbaumCnfizer(const Config &config) : FormulaVisitor{config, "PlaistedGreenbaumCnfizer"} {}

  /**
   * Convert a @p f into an equi-satisfiable formula @c f' in CNF.
   * @param f A formula to be converted.
   * @return A vector of clauses.
   */
  std::vector<Formula> Convert(const Formula &f);

  /**
   * Return a const reference of `vars_` member.
   * @return a const reference of `vars_` member.
   */
  [[nodiscard]] const std::vector<Variable> &vars() const { return vars_; }

 private:
  Formula Visit(const Formula &f) override;
  Formula VisitConjunction(const Formula &f) override;
  Formula VisitDisjunction(const Formula &f) override;
  Formula VisitNegation(const Formula &f) override;
  Formula VisitForall(const Formula &f) override;
  const Nnfizer nnfizer_{};

  const NaiveCnfizer
      naive_cnfizer_{};  ///< Naive CNFizer. Used to transform nested formulas inside universal quantification.

  std::vector<Formula>
      aux_;  ///< Auxiliary clauses collected during conversion. @note It is cleared at the beginning of `Convert` call.

  std::vector<Variable>
      vars_;  ///< Variables generated during conversion. @note It is cleared at the beginning of `Convert` call.

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula, PlaistedGreenbaumCnfizer>(PlaistedGreenbaumCnfizer *,
                                                                                  const Formula &);
};

}  // namespace dlinear
