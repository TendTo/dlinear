/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @copyrignt 2017 Toyota Research Institute (dreal4)
 * @licence BSD 3-Clause License
 * Nnfizer class.
 */
#pragma once

#include "dlinear/symbolic/FormulaVisitor.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Config.h"

namespace dlinear {

/**
 * Implementation of NNF (Negation Normal Form) conversion.
 *
 * When `push_negation_into_relationals` is true, it pushes negations into relational formulas by flipping relational
 * @par Example:
 *   @f$ ¬(x \ge 10) @f$ becomes @f$ (x < 10) @f$
 * @see [Wikipedia](https://en.wikipedia.org/wiki/Negation_normal_form).
 */
class Nnfizer : public FormulaVisitor<bool, bool> {
 public:
  explicit Nnfizer(const Config &config);
  /**
   * Convert a @p f into an equivalent formula @c f' in NNF.
   * @param f formula to be converted
   * @param push_negation_into_relationals whether to push negation into relational formulas
   * @return nnf converted formula
   */
  [[nodiscard]] Formula Process(const Formula &f, bool push_negation_into_relationals = false) const;
  [[nodiscard]] Formula operator()(const Formula &f, bool push_negation_into_relationals = false) const;

 private:
  /**
   * Convert @p f into an equivalent formula @c f' in NNF. The parameter @p polarity
   * is to indicate whether it processes @c f (if @p polarity is true) or @c ¬f (if @p polarity is false).
   * @param f formula to be converted
   * @param polarity whether to process @c f or @c ¬f
   * @param push_negation_into_relationals whether to push negation into relational formulas
   * @return nnf converted formula
   */
  [[nodiscard]] Formula VisitFalse(const Formula &f, bool polarity, bool push_negation_into_relationals) const override;
  [[nodiscard]] Formula VisitTrue(const Formula &f, bool polarity, bool push_negation_into_relationals) const override;
  [[nodiscard]] Formula VisitVariable(const Formula &f, bool polarity,
                                      bool push_negation_into_relationals) const override;
  [[nodiscard]] Formula VisitEqualTo(const Formula &f, bool polarity,
                                     bool push_negation_into_relationals) const override;
  [[nodiscard]] Formula VisitNotEqualTo(const Formula &f, bool polarity,
                                        bool push_negation_into_relationals) const override;
  [[nodiscard]] Formula VisitGreaterThan(const Formula &f, bool polarity,
                                         bool push_negation_into_relationals) const override;
  [[nodiscard]] Formula VisitGreaterThanOrEqualTo(const Formula &f, bool polarity,
                                                  bool push_negation_into_relationals) const override;
  [[nodiscard]] Formula VisitLessThan(const Formula &f, bool polarity,
                                      bool push_negation_into_relationals) const override;
  [[nodiscard]] Formula VisitLessThanOrEqualTo(const Formula &f, bool polarity,
                                               bool push_negation_into_relationals) const override;
  [[nodiscard]] Formula VisitConjunction(const Formula &f, bool polarity,
                                         bool push_negation_into_relationals) const override;
  [[nodiscard]] Formula VisitDisjunction(const Formula &f, bool polarity,
                                         bool push_negation_into_relationals) const override;
  [[nodiscard]] Formula VisitNegation(const Formula &f, bool polarity,
                                      bool push_negation_into_relationals) const override;
  [[nodiscard]] Formula VisitForall(const Formula &f, bool polarity,
                                    bool push_negation_into_relationals) const override;
};
}  // namespace dlinear
