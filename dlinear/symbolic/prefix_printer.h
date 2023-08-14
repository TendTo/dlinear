#pragma once

#include <ios>
#include <ostream>
#include <string>
#include <sstream>

#include "dlinear/symbolic/symbolic.h"

using std::string;
using std::ostream;
using std::streamsize;
using std::ostringstream;
using std::runtime_error;

namespace dlinear {

/**
 * This class is used to print expressions and formulas in prefix-form.
 * It is mainly used for debugging purposes.
 */
class PrefixPrinter {
 public:
  /**
   * Constructs a PrefixPrinter with @p os. It temporarily sets the precision of
   * @p os to the maximum precision.
   * @param os stream to print to.
   */
  explicit PrefixPrinter(ostream &os);

  PrefixPrinter(const PrefixPrinter &) = delete;
  PrefixPrinter(PrefixPrinter &&) = delete;
  PrefixPrinter &operator=(const PrefixPrinter &) = delete;
  PrefixPrinter &operator=(PrefixPrinter &&) = delete;

  /// Destroys this. It restores the original precision of the ostream.
  /** Destructor */
  ~PrefixPrinter();

  /// Prints the prefix form of the expression @p e to the ostream.
  ostream &Print(const Expression &e);

  /// Prints the prefix form of the formula @p f to the ostream.
  ostream &Print(const Formula &f);

 private:
  ostream &VisitVariable(const Expression &e);
  ostream &VisitConstant(const Expression &e);
  ostream &VisitAddition(const Expression &e);
  ostream &VisitMultiplication(const Expression &e);
  ostream &VisitDivision(const Expression &e);
  ostream &VisitLog(const Expression &e);
  ostream &VisitAbs(const Expression &e);
  ostream &VisitExp(const Expression &e);
  ostream &VisitSqrt(const Expression &e);
  ostream &VisitPow(const Expression &e);
  ostream &VisitSin(const Expression &e);
  ostream &VisitCos(const Expression &e);
  ostream &VisitTan(const Expression &e);
  ostream &VisitAsin(const Expression &e);
  ostream &VisitAcos(const Expression &e);
  ostream &VisitAtan(const Expression &e);
  ostream &VisitAtan2(const Expression &e);
  ostream &VisitSinh(const Expression &e);
  ostream &VisitCosh(const Expression &e);
  ostream &VisitTanh(const Expression &e);
  ostream &VisitMin(const Expression &e);
  ostream &VisitMax(const Expression &e);
  ostream &VisitIfThenElse(const Expression &e);
  static ostream &VisitUninterpretedFunction(const Expression &e);

  ostream &VisitFalse(const Formula &f);
  ostream &VisitTrue(const Formula &f);
  ostream &VisitVariable(const Formula &f);
  ostream &VisitEqualTo(const Formula &f);
  ostream &VisitNotEqualTo(const Formula &f);
  ostream &VisitGreaterThan(const Formula &f);
  ostream &VisitGreaterThanOrEqualTo(const Formula &f);
  ostream &VisitLessThan(const Formula &f);
  ostream &VisitLessThanOrEqualTo(const Formula &f);
  ostream &VisitConjunction(const Formula &f);
  ostream &VisitDisjunction(const Formula &f);
  ostream &VisitNegation(const Formula &f);
  static ostream &VisitForall(const Formula &f);

  ostream &VisitUnaryFunction(const string &name,
                              const Expression &e);
  ostream &VisitBinaryFunction(const string &name,
                               const Expression &e);

  // Makes VisitExpression a friend of this class so that it can use private
  // operator()s.
  friend ostream &drake::symbolic::VisitExpression<ostream &>(PrefixPrinter *, const Expression &e);

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend ostream &drake::symbolic::VisitFormula<ostream &>(PrefixPrinter *, const Formula &f);

  ostream &os_;
  streamsize old_precision_{};
};

/// Returns the prefix-string representation of the expression @p e.
string ToPrefix(const Expression &e);

/// Returns the prefix-string representation of the formula @p e.
string ToPrefix(const Formula &f);

}  // namespace dlinear
