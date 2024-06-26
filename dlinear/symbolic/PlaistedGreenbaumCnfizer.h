/**
 * @file PlaistedGreenbaumCnfizer.h
 * @author dlinear
 * @date 18 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
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

class PlaistedGreenbaumCnfizer : public FormulaVisitor {
 public:
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
