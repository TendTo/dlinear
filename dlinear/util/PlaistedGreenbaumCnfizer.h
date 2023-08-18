/**
 * @file PlaistedGreenbaumCnfizer.h
 * @author dlinear
 * @date 18 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */

#ifndef DLINEAR5_DLINEAR_UTIL_PLAISTEDGREENBAUMCNFIZER_H_
#define DLINEAR5_DLINEAR_UTIL_PLAISTEDGREENBAUMCNFIZER_H_

#include <vector>

#include "dlinear/symbolic/symbolic.h"
#include "dlinear/symbolic/NaiveCnfizer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"

namespace dlinear {

class PlaistedGreenbaumCnfizer {
 public:
  /// Convert @p f into an equi-satisfiable formula @c f' in CNF.
  std::vector<Formula> Convert(const Formula &f);

  /// Returns a const reference of `map_` member.
  ///
  /// @note that this member `map_` is cleared at the beginning of `Convert`
  /// method.
  [[nodiscard]] const std::vector<Variable> &vars() const { return vars_; }

 private:
  Formula Visit(const Formula &f);
  Formula VisitFalse(const Formula &f);
  Formula VisitTrue(const Formula &f);
  Formula VisitVariable(const Formula &f);
  Formula VisitEqualTo(const Formula &f);
  Formula VisitNotEqualTo(const Formula &f);
  Formula VisitGreaterThan(const Formula &f);
  Formula VisitGreaterThanOrEqualTo(const Formula &f);
  Formula VisitLessThan(const Formula &f);
  Formula VisitLessThanOrEqualTo(const Formula &f);
  Formula VisitConjunction(const Formula &f);
  Formula VisitDisjunction(const Formula &f);
  Formula VisitNegation(const Formula &f);
  Formula VisitForall(const Formula &f);

  const Nnfizer nnfizer_{};

  // To transform nested formulas inside universal quantifications.
  const NaiveCnfizer naive_cnfizer_{};

  // Set of auxilliary clauses collected during conversion.
  //
  // @note that this aux_ is cleared at the beginning of `Convert`
  // call.
  std::vector<Formula> aux_;

  // Set of variables generated during conversion.
  //
  // @note that these vars_ is cleared at the beginning of `Convert`
  // call.
  std::vector<Variable> vars_;

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula, PlaistedGreenbaumCnfizer>(PlaistedGreenbaumCnfizer *,
                                                                                  const Formula &);
};

} // dlinear

#endif //DLINEAR5_DLINEAR_UTIL_PLAISTEDGREENBAUMCNFIZER_H_
