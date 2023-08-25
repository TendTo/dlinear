/**
 * @file TseitinCnfizer.h
 * @author dlinear
 * @date 19 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */

#ifndef DLINEAR5_DLINEAR_SYMBOLIC_TSEITINCNFIZER_H_
#define DLINEAR5_DLINEAR_SYMBOLIC_TSEITINCNFIZER_H_

#include <map>
#include <unordered_map>
#include <vector>
#include <algorithm>
#include <atomic>
#include <iostream>
#include <iterator>
#include <set>
#include <string>

#include "dlinear/symbolic/symbolic.h"
#include "dlinear/symbolic/NaiveCnfizer.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"
#include "dlinear//util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/symbolic/FormulaVisitor.h"

namespace dlinear {

/// Transforms a symbolic formula @p f into an equi-satisfiable CNF
/// formula by introducing extra Boolean variables (Tseitin transformation).
class TseitinCnfizer : public FormulaVisitor {
 public:
  /// Convert @p f into an equi-satisfiable formula @c f' in CNF.
  std::vector<Formula> Convert(const Formula &f);

  /// Returns a const reference of `map_` member.
  ///
  /// @note that this member `map_` is cleared at the beginning of `Convert`
  /// method.
  const std::map<Variable, Formula> &map() const { return map_; }

 private:
  Formula Visit(const Formula &f) override;
  Formula VisitConjunction(const Formula &f) override;
  Formula VisitDisjunction(const Formula &f) override;
  Formula VisitNegation(const Formula &f) override;
  Formula VisitForall(const Formula &f) override;

  // Maps a temporary variable, which is introduced by a Tseitin
  // transformation, to a corresponding Formula.
  //
  // @note that this map_ is cleared at the beginning of `Convert`
  // call.
  std::map<Variable, Formula> map_;

  // To transform nested formulas inside of universal quantifications.
  const NaiveCnfizer naive_cnfizer_{};

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula, TseitinCnfizer>(TseitinCnfizer *, const Formula &);
};

} // namespace dlinear

#endif //DLINEAR5_DLINEAR_SYMBOLIC_TSEITINCNFIZER_H_
