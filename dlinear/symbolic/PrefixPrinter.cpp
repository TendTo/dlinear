/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "PrefixPrinter.h"

#include <map>
#include <set>
#include <sstream>  // IWYU pragma: keep for std::stringstream
#include <stdexcept>
#include <utility>

#include "dlinear/libs/libgmp.h"
#include "dlinear/symbolic/literal.h"

namespace dlinear {

PrefixPrinter::PrefixPrinter(std::ostream &os, const Config &config)
    : GenericFormulaVisitor<std::ostream &>(config, "PrefixPrinter"),
      GenericExpressionVisitor<std::ostream &>(config, "PrefixPrinter"),
      os_{os},
      old_precision_{os.precision()} {}

PrefixPrinter::~PrefixPrinter() { os_.precision(old_precision_); }

std::ostream &PrefixPrinter::Print(const Expression &e) const { return GenericExpressionVisitor::VisitExpression(e); }
std::ostream &PrefixPrinter::operator()(const Expression &e) const { return Print(e); }

std::ostream &PrefixPrinter::Print(const Formula &f) const { return VisitFormula(f); }
std::ostream &PrefixPrinter::operator()(const Formula &f) const { return Print(f); }

std::ostream &PrefixPrinter::VisitVariable(const Expression &e) const { return os_ << get_variable(e); }

std::ostream &PrefixPrinter::VisitConstant(const Expression &e) const {
  const mpq_class &constant{get_constant_value(e)};
  bool print_den = constant.get_den() != 1;
  if (print_den) {
    os_ << "(/ ";
  }
  os_ << constant.get_num();
  if (print_den) {
    os_ << " ";
    os_ << constant.get_den();
    os_ << ")";
  }
  return os_;
}

std::ostream &PrefixPrinter::VisitUnaryFunction(const std::string &name, const Expression &e) const {
  os_ << "(" << name << " ";
  Print(get_argument(e));
  return os_ << ")";
}

std::ostream &PrefixPrinter::VisitBinaryFunction(const std::string &name, const Expression &e) const {
  os_ << "(" << name << " ";
  Print(get_first_argument(e));
  os_ << " ";
  Print(get_second_argument(e));
  return os_ << ")";
}

std::ostream &PrefixPrinter::VisitAddition(const Expression &e) const {
  const mpq_class &constant{get_constant_in_addition(e)};
  os_ << "(+";
  if (constant != 0.0) {
    os_ << " ";
    VisitConstant(constant);
  }
  for (const auto &p : get_expr_to_coeff_map_in_addition(e)) {
    const Expression &e_i{p.first};
    const mpq_class &c_i{p.second};
    os_ << " ";
    if (c_i == 1.0) {
      Print(e_i);
    } else {
      os_ << "(* ";
      VisitConstant(c_i);
      os_ << " ";
      Print(e_i);
      os_ << ")";
    }
  }
  return os_ << ")";
}

std::ostream &PrefixPrinter::VisitMultiplication(const Expression &e) const {
  const mpq_class &constant{get_constant_in_multiplication(e)};
  os_ << "(*";
  if (constant != 1.0) {
    os_ << " ";
    VisitConstant(constant);
  }
  for (const auto &p : get_base_to_exponent_map_in_multiplication(e)) {
    const Expression &b_i{p.first};
    const Expression &e_i{p.second};
    os_ << " ";
    if (is_one(e_i)) {
      Print(b_i);
    } else {
      os_ << "(^ ";
      Print(b_i);
      os_ << " ";
      Print(e_i);
      os_ << ")";
    }
  }
  return os_ << ")";
}

std::ostream &PrefixPrinter::VisitDivision(const Expression &e) const { return VisitBinaryFunction("/", e); }

std::ostream &PrefixPrinter::VisitLog(const Expression &e) const { return VisitUnaryFunction("log", e); }

std::ostream &PrefixPrinter::VisitAbs(const Expression &e) const { return VisitUnaryFunction("abs", e); }

std::ostream &PrefixPrinter::VisitExp(const Expression &e) const { return VisitUnaryFunction("exp", e); }

std::ostream &PrefixPrinter::VisitSqrt(const Expression &e) const { return VisitUnaryFunction("sqrt", e); }

std::ostream &PrefixPrinter::VisitPow(const Expression &e) const { return VisitBinaryFunction("^", e); }

std::ostream &PrefixPrinter::VisitSin(const Expression &e) const { return VisitUnaryFunction("sin", e); }

std::ostream &PrefixPrinter::VisitCos(const Expression &e) const { return VisitUnaryFunction("cos", e); }

std::ostream &PrefixPrinter::VisitTan(const Expression &e) const { return VisitUnaryFunction("tan", e); }

std::ostream &PrefixPrinter::VisitAsin(const Expression &e) const { return VisitUnaryFunction("asin", e); }

std::ostream &PrefixPrinter::VisitAcos(const Expression &e) const { return VisitUnaryFunction("acos", e); }

std::ostream &PrefixPrinter::VisitAtan(const Expression &e) const { return VisitUnaryFunction("atan", e); }

std::ostream &PrefixPrinter::VisitAtan2(const Expression &e) const { return VisitBinaryFunction("atan2", e); }

std::ostream &PrefixPrinter::VisitSinh(const Expression &e) const { return VisitUnaryFunction("sinh", e); }

std::ostream &PrefixPrinter::VisitCosh(const Expression &e) const { return VisitUnaryFunction("cosh", e); }

std::ostream &PrefixPrinter::VisitTanh(const Expression &e) const { return VisitUnaryFunction("tanh", e); }

std::ostream &PrefixPrinter::VisitMin(const Expression &e) const { return VisitBinaryFunction("min", e); }

std::ostream &PrefixPrinter::VisitMax(const Expression &e) const { return VisitBinaryFunction("max", e); }

std::ostream &PrefixPrinter::VisitIfThenElse(const Expression &e) const {
  os_ << "(ite ";
  Print(get_conditional_formula(e));
  os_ << " ";
  Print(get_then_expression(e));
  os_ << " ";
  Print(get_else_expression(e));
  return os_ << ")";
}

std::ostream &PrefixPrinter::VisitUninterpretedFunction(const Expression &) const {
  throw std::runtime_error("Not implemented.");
}

std::ostream &PrefixPrinter::VisitFalse(const Formula &) const { return os_ << "false"; }

std::ostream &PrefixPrinter::VisitTrue(const Formula &) const { return os_ << "true"; }

std::ostream &PrefixPrinter::VisitVariable(const Formula &f) const { return os_ << get_variable(f); }

std::ostream &PrefixPrinter::VisitEqualTo(const Formula &f) const {
  os_ << "(= ";
  Print(get_lhs_expression(f));
  os_ << " ";
  Print(get_rhs_expression(f));
  return os_ << ")";
}

std::ostream &PrefixPrinter::VisitNotEqualTo(const Formula &f) const {
  os_ << "(not (= ";
  Print(get_lhs_expression(f));
  os_ << " ";
  Print(get_rhs_expression(f));
  return os_ << "))";
}

std::ostream &PrefixPrinter::VisitGreaterThan(const Formula &f) const {
  os_ << "(> ";
  Print(get_lhs_expression(f));
  os_ << " ";
  Print(get_rhs_expression(f));
  return os_ << ")";
}

std::ostream &PrefixPrinter::VisitGreaterThanOrEqualTo(const Formula &f) const {
  os_ << "(>= ";
  Print(get_lhs_expression(f));
  os_ << " ";
  Print(get_rhs_expression(f));
  return os_ << ")";
}

std::ostream &PrefixPrinter::VisitLessThan(const Formula &f) const {
  os_ << "(< ";
  Print(get_lhs_expression(f));
  os_ << " ";
  Print(get_rhs_expression(f));
  return os_ << ")";
}

std::ostream &PrefixPrinter::VisitLessThanOrEqualTo(const Formula &f) const {
  os_ << "(<= ";
  Print(get_lhs_expression(f));
  os_ << " ";
  Print(get_rhs_expression(f));
  return os_ << ")";
}

std::ostream &PrefixPrinter::VisitConjunction(const Formula &f) const {
  os_ << "(and";
  for (const auto &f_i : get_operands(f)) {
    os_ << " ";
    Print(f_i);
  }
  return os_ << ")";
}

std::ostream &PrefixPrinter::VisitDisjunction(const Formula &f) const {
  os_ << "(or";
  for (const auto &f_i : get_operands(f)) {
    os_ << " ";
    Print(f_i);
  }
  return os_ << ")";
}

std::ostream &PrefixPrinter::VisitNegation(const Formula &f) const {
  os_ << "(not ";
  Print(get_operand(f));
  return os_ << ")";
}

std::ostream &PrefixPrinter::VisitForall(const Formula &) const { throw std::runtime_error("Not implemented."); }

std::string ToPrefix(const Expression &e) {
  std::ostringstream oss;
  static Config config;
  config.m_with_timings() = false;
  PrefixPrinter pp{oss, config};
  pp.Print(e);
  return oss.str();
}

std::string ToPrefix(const Formula &f) {
  std::ostringstream oss;
  static Config config;
  config.m_with_timings() = false;
  PrefixPrinter pp{oss, config};
  pp.Print(f);
  return oss.str();
}

}  // namespace dlinear
