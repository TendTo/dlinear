/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * PrefixPrinter class.
 */
#pragma once

#include <ios>
#include <string>

#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

/**
 * Print expressions and formulas in prefix-form.
 *
 * It is mainly used for debugging purposes.
 */
class PrefixPrinter {
 public:
  /**
   * Constructs a new PrefixPrinter object with @p os.
   *
   * It temporarily sets the precision of @p os to the maximum precision.
   * @param os stream to print to.
   */
  explicit PrefixPrinter(std::ostream &os);

  PrefixPrinter(const PrefixPrinter &) = delete;
  PrefixPrinter(PrefixPrinter &&) = delete;
  PrefixPrinter &operator=(const PrefixPrinter &) = delete;
  PrefixPrinter &operator=(PrefixPrinter &&) = delete;

  /** Restore the original precision of the ostream. */
  ~PrefixPrinter();

  /**
   * Print the prefix form of the expression @p e to the ostream.
   * @param e expression to print
   * @return updated ostream
   */
  std::ostream &Print(const Expression &e);

  /**
   * Print the prefix form of the formula @p f to the ostream.
   * @param f formula to print
   * @return updated ostream
   */
  std::ostream &Print(const Formula &f);

 private:
  std::ostream &VisitVariable(const Expression &e);
  std::ostream &VisitConstant(const Expression &e);
  std::ostream &VisitAddition(const Expression &e);
  std::ostream &VisitMultiplication(const Expression &e);
  std::ostream &VisitDivision(const Expression &e);
  std::ostream &VisitLog(const Expression &e);
  std::ostream &VisitAbs(const Expression &e);
  std::ostream &VisitExp(const Expression &e);
  std::ostream &VisitSqrt(const Expression &e);
  std::ostream &VisitPow(const Expression &e);
  std::ostream &VisitSin(const Expression &e);
  std::ostream &VisitCos(const Expression &e);
  std::ostream &VisitTan(const Expression &e);
  std::ostream &VisitAsin(const Expression &e);
  std::ostream &VisitAcos(const Expression &e);
  std::ostream &VisitAtan(const Expression &e);
  std::ostream &VisitAtan2(const Expression &e);
  std::ostream &VisitSinh(const Expression &e);
  std::ostream &VisitCosh(const Expression &e);
  std::ostream &VisitTanh(const Expression &e);
  std::ostream &VisitMin(const Expression &e);
  std::ostream &VisitMax(const Expression &e);
  std::ostream &VisitIfThenElse(const Expression &e);
  static std::ostream &VisitUninterpretedFunction(const Expression &e);

  std::ostream &VisitFalse(const Formula &f);
  std::ostream &VisitTrue(const Formula &f);
  std::ostream &VisitVariable(const Formula &f);
  std::ostream &VisitEqualTo(const Formula &f);
  std::ostream &VisitNotEqualTo(const Formula &f);
  std::ostream &VisitGreaterThan(const Formula &f);
  std::ostream &VisitGreaterThanOrEqualTo(const Formula &f);
  std::ostream &VisitLessThan(const Formula &f);
  std::ostream &VisitLessThanOrEqualTo(const Formula &f);
  std::ostream &VisitConjunction(const Formula &f);
  std::ostream &VisitDisjunction(const Formula &f);
  std::ostream &VisitNegation(const Formula &f);
  static std::ostream &VisitForall(const Formula &f);

  std::ostream &VisitUnaryFunction(const std::string &name, const Expression &e);
  std::ostream &VisitBinaryFunction(const std::string &name, const Expression &e);

  // Makes VisitExpression a friend of this class so that it can use private
  // operator()s.
  friend std::ostream &drake::symbolic::VisitExpression<std::ostream &>(PrefixPrinter *, const Expression &e);

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend std::ostream &drake::symbolic::VisitFormula<std::ostream &>(PrefixPrinter *, const Formula &f);

  std::ostream &os_;                 ///< Stream to print to.
  std::streamsize old_precision_{};  ///< Original precision of the stream.
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
