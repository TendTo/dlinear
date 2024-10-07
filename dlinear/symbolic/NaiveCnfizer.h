/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * NaiveCnfizer class.
 */
#pragma once

#include "dlinear/symbolic/FormulaVisitor.h"
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
class NaiveCnfizer : public FormulaVisitor {
 public:
  /**
   * Construct a new NaiveCnfizer object with the given @p config.
   * @param config configuration
   */
  explicit NaiveCnfizer(const Config &config) : FormulaVisitor{config, "NaiveCnfizer"} {}

  /**
   * Convert a @p f into an equivalent formula @c f' in CNF.
   * @param f formula to be converted
   * @return cnf converted formula
   */
  [[nodiscard]] Formula Convert(const Formula &f);

 private:
  [[nodiscard]] Formula VisitEqualTo(const Formula &f) override;
  [[nodiscard]] Formula VisitNotEqualTo(const Formula &f) override;
  [[nodiscard]] Formula VisitConjunction(const Formula &f) override;
  [[nodiscard]] Formula VisitDisjunction(const Formula &f) override;
  [[nodiscard]] Formula VisitNegation(const Formula &f) override;
  [[nodiscard]] Formula VisitForall(const Formula &f) override;

  Nnfizer nnfizer_{config_};  ///< NNFizer. Used to convert the formula into NNF.
};

}  // namespace dlinear
