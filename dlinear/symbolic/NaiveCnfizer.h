/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * NaiveCnfizer class.
 */
#pragma once

#include "dlinear/symbolic/Nnfizer.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

/**
 * Transforms a symbolic formula @p f into a CNF formula by preserving its semantics.
 *
 * @note This transform can increase the size exponentially.
 * We are using this transformation in TseitinCnfizer
 * when we process the nested formula in a universally quantified formula.
 */
class NaiveCnfizer {
 public:
  /**
   * Convert a @p f into an equivalent formula @c f' in CNF.
   * @param f formula to be converted
   * @return cnf converted formula
   */
  [[nodiscard]] Formula Convert(const Formula &f) const;

 private:
  [[nodiscard]] Formula Visit(const Formula &f) const;
  [[nodiscard]] Formula VisitFalse(const Formula &f) const;
  [[nodiscard]] Formula VisitTrue(const Formula &f) const;
  [[nodiscard]] Formula VisitVariable(const Formula &f) const;
  [[nodiscard]] Formula VisitEqualTo(const Formula &f) const;
  [[nodiscard]] Formula VisitNotEqualTo(const Formula &f) const;
  [[nodiscard]] Formula VisitGreaterThan(const Formula &f) const;
  [[nodiscard]] Formula VisitGreaterThanOrEqualTo(const Formula &f) const;
  [[nodiscard]] Formula VisitLessThan(const Formula &f) const;
  [[nodiscard]] Formula VisitLessThanOrEqualTo(const Formula &f) const;
  [[nodiscard]] Formula VisitConjunction(const Formula &f) const;
  [[nodiscard]] Formula VisitDisjunction(const Formula &f) const;
  [[nodiscard]] Formula VisitNegation(const Formula &f) const;
  [[nodiscard]] Formula VisitForall(const Formula &f) const;

  const Nnfizer nnfizer_{};  ///< NNFizer. Used to convert the formula into NNF.

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula>(const NaiveCnfizer *, const Formula &);
};

}  // namespace dlinear
