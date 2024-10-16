/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * PrefixPrinter class.
 */
#pragma once

#include <ios>
#include <string>

#include "dlinear/symbolic/GenericExpressionVisitor.h"
#include "dlinear/symbolic/GenericFormulaVisitor.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

/**
 * Print expressions and formulas in prefix-form.
 *
 * It is mainly used for debugging purposes.
 */
class PrefixPrinter : public GenericFormulaVisitor<std::ostream &>, public GenericExpressionVisitor<std::ostream &> {
 public:
  /**
   * Constructs a new PrefixPrinter object with @p os.
   *
   * It temporarily sets the precision of @p os to the maximum precision.
   * @param os stream to print to.
   */
  explicit PrefixPrinter(std::ostream &os, const Config &config = Config{});

  PrefixPrinter(const PrefixPrinter &) = delete;
  PrefixPrinter(PrefixPrinter &&) = delete;
  PrefixPrinter &operator=(const PrefixPrinter &) = delete;
  PrefixPrinter &operator=(PrefixPrinter &&) = delete;

  /** Restore the original precision of the ostream. */
  ~PrefixPrinter() override;

  /**
   * Print the prefix form of the expression @p e to the ostream.
   * @param e expression to print
   * @return updated ostream
   */
  std::ostream &Print(const Expression &e) const;
  std::ostream &operator()(const Expression &e) const;

  /**
   * Print the prefix form of the formula @p f to the ostream.
   * @param f formula to print
   * @return updated ostream
   */
  std::ostream &Print(const Formula &f) const;
  std::ostream &operator()(const Formula &f) const;

 private:
  std::ostream &VisitVariable(const Expression &e) const override;
  std::ostream &VisitConstant(const Expression &e) const override;
  std::ostream &VisitAddition(const Expression &e) const override;
  std::ostream &VisitMultiplication(const Expression &e) const override;
  std::ostream &VisitDivision(const Expression &e) const override;
  std::ostream &VisitLog(const Expression &e) const override;
  std::ostream &VisitAbs(const Expression &e) const override;
  std::ostream &VisitExp(const Expression &e) const override;
  std::ostream &VisitSqrt(const Expression &e) const override;
  std::ostream &VisitPow(const Expression &e) const override;
  std::ostream &VisitSin(const Expression &e) const override;
  std::ostream &VisitCos(const Expression &e) const override;
  std::ostream &VisitTan(const Expression &e) const override;
  std::ostream &VisitAsin(const Expression &e) const override;
  std::ostream &VisitAcos(const Expression &e) const override;
  std::ostream &VisitAtan(const Expression &e) const override;
  std::ostream &VisitAtan2(const Expression &e) const override;
  std::ostream &VisitSinh(const Expression &e) const override;
  std::ostream &VisitCosh(const Expression &e) const override;
  std::ostream &VisitTanh(const Expression &e) const override;
  std::ostream &VisitMin(const Expression &e) const override;
  std::ostream &VisitMax(const Expression &e) const override;
  std::ostream &VisitIfThenElse(const Expression &e) const override;
  std::ostream &VisitUninterpretedFunction(const Expression &e) const override;

  std::ostream &VisitFalse(const Formula &f) const override;
  std::ostream &VisitTrue(const Formula &f) const override;
  std::ostream &VisitVariable(const Formula &f) const override;
  std::ostream &VisitEqualTo(const Formula &f) const override;
  std::ostream &VisitNotEqualTo(const Formula &f) const override;
  std::ostream &VisitGreaterThan(const Formula &f) const override;
  std::ostream &VisitGreaterThanOrEqualTo(const Formula &f) const override;
  std::ostream &VisitLessThan(const Formula &f) const override;
  std::ostream &VisitLessThanOrEqualTo(const Formula &f) const override;
  std::ostream &VisitConjunction(const Formula &f) const override;
  std::ostream &VisitDisjunction(const Formula &f) const override;
  std::ostream &VisitNegation(const Formula &f) const override;
  std::ostream &VisitForall(const Formula &f) const override;

  std::ostream &VisitUnaryFunction(const std::string &name, const Expression &e) const;
  std::ostream &VisitBinaryFunction(const std::string &name, const Expression &e) const;

  std::ostream &os_;                     ///< Stream to print to.
  const std::streamsize old_precision_;  ///< Original precision of the stream.
};

/**
 * Produce the prefix-string representation of the expression @p e.
 * @param e expression to convert
 * @return prefix-string representation of the expression
 */
std::string ToPrefix(const Expression &e);

/**
 * Produce the prefix-string representation of the formula @p f.
 * @param f formula to convert
 * @return prefix-string representation of the formula
 */
std::string ToPrefix(const Formula &f);

}  // namespace dlinear
