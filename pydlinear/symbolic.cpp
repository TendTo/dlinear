/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#ifndef DLINEAR_PYDLINEAR
#error DLINEAR_PYDLINEAR is not defined. Ensure you are building with the option '--config=pydlinear'
#endif

#include "dlinear/symbolic/symbolic.h"

#include <pybind11/operators.h>
#include <pybind11/stl.h>

#include "pydlinear.h"

namespace py = pybind11;
using namespace dlinear;

void init_symbolic(py::module_ &m) {
  auto VariableClass = py::class_<Variable>(m, "Variable");
  auto VariablesClass = py::class_<Variables>(m, "Variables");
  auto ExpressionClass = py::class_<Expression>(m, "Expression");
  auto FormulaClass = py::class_<Formula>(m, "Formula");

  py::enum_<Variable::Type>(m, "VariableType")
      .value("Real", Variable::Type::CONTINUOUS)
      .value("Int", Variable::Type::INTEGER)
      .value("Bool", Variable::Type::BOOLEAN)
      .value("Binary", Variable::Type::BINARY);

  FormulaClass.def(py::init<const Variable &>())
      .def("GetFreeVariables", &Formula::GetFreeVariables)
      .def("EqualTo", &Formula::EqualTo)
      .def("Evaluate", [](const Formula &self) { return self.Evaluate(); })
      .def("Substitute",
           [](const Formula &self, const Variable &var, const Expression &e) { return self.Substitute(var, e); })
      .def("to_string", &Formula::to_string)
      .def("to_smt2_string", &Formula::to_smt2_string)
      .def("__str__", &Formula::to_string)
      .def("__repr__",
           [](const Formula &self) { return (std::stringstream{} << "<Formula '" << self.to_string() << "'>").str(); })
      .def("__eq__", [](const Formula &self, const Formula &other) { return self.EqualTo(other); })
      .def("__ne__", [](const Formula &self, const Formula &other) { return !self.EqualTo(other); })
      .def("__hash__", [](const Formula &self) { return std::hash<Formula>{}(self); })
      .def("__nonzero__", [](const Formula &f) { return f.Evaluate(); })
      // EQ(==).
      .def(py::self == Variable())
      // NEQ(!=).
      .def(py::self != Variable())
      .def_static("TRUE", &Formula::True)
      .def_static("FALSE", &Formula::False);

  VariableClass.def(py::init<const std::string &>())
      .def(py::init<const std::string &, Variable::Type>())
      .def("__abs__", [](const Variable &self) { return abs(self); })
      .def("get_id", &Variable::get_id)
      .def("get_type", &Variable::get_type)
      .def("__str__", &Variable::to_string)
      .def(
          "__repr__",
          [](const Variable &self) { return (std::stringstream{} << "<Variable '" << self.to_string() << "'>").str(); })
      .def("__hash__", [](const Variable &self) { return std::hash<Variable>{}(self); })
      // Addition.
      .def(py::self + py::self)
      .def(py::self + double())
      .def(double() + py::self)
      // Subtraction.
      .def(py::self - py::self)
      .def(py::self - double())
      .def(double() - py::self)
      // Multiplication.
      .def(py::self * py::self)
      .def(py::self * double())
      .def(double() * py::self)
      // Division.
      .def(py::self / py::self)
      .def(py::self / double())
      .def(double() / py::self)
      // Pow.
      .def(
          "__pow__", [](const Variable &self, const Expression &other) { return pow(self, other); }, py::is_operator())
      // Unary Plus.
      .def(+py::self)
      // Unary Minus.
      .def(-py::self)
      // LT(<).
      // Note that for `double < Variable` case, the reflected op ('>' in this
      // case) is called. For example, `1 < x` will return `x > 1`.
      .def(py::self < py::self)
      .def(py::self < double())
      // LE(<=).
      .def(py::self <= py::self)
      .def(py::self <= double())
      // GT(>).
      .def(py::self > py::self)
      .def(py::self > double())
      // GE(>=).
      .def(py::self >= py::self)
      .def(py::self >= double())
      // EQ(==).
      .def(py::self == py::self)
      .def(py::self == double())
      // NE(!=).
      .def(py::self != py::self)
      .def(py::self != double());

  VariablesClass.def(py::init<>())
      .def(py::init([](const std::vector<Variable> &vec) {
        Variables variables;
        variables.insert(vec.begin(), vec.end());
        return variables;
      }))
      .def("size", &Variables::size)
      .def("__len__", &Variables::size)
      .def("empty", &Variables::empty)
      .def("__str__", &Variables::to_string)
      .def("__repr__",
           [](const Variables &self) {
             return (std::stringstream{} << "<Variables '" << self.to_string() << "'>").str();
           })
      .def("to_string", &Variables::to_string)
      .def("__hash__", [](const Variables &self) { return self.get_hash(); })
      .def("insert", [](Variables &self, const Variable &var) { self.insert(var); })
      .def("insert", [](Variables &self, const Variables &vars) { self.insert(vars); })
      .def("erase", [](Variables &self, const Variable &var) { return self.erase(var); })
      .def("erase", [](Variables &self, const Variables &vars) { return self.erase(vars); })
      .def("include", &Variables::include)
      .def("__contains__", &Variables::include)
      .def("IsSubsetOf", &Variables::IsSubsetOf)
      .def("IsSupersetOf", &Variables::IsSupersetOf)
      .def("IsStrictSubsetOf", &Variables::IsStrictSubsetOf)
      .def("IsStrictSupersetOf", &Variables::IsStrictSupersetOf)
      .def(
          "__iter__", [](const Variables &vars) { return py::make_iterator(vars.begin(), vars.end()); },
          py::keep_alive<0, 1>() /* Essential: keep object alive while iterator exists */)
      .def(py::self == py::self)
      .def(py::self < py::self)
      .def(py::self + py::self)
      .def(py::self + Variable())
      .def(Variable() + py::self)
      .def(py::self - py::self)
      .def(py::self - Variable());

  ExpressionClass.def(py::init<>())
      .def(py::init<>([](double b) { return std::make_unique<Expression>(b); }))
      .def(py::init<>([](const Variable &var) { return std::make_unique<Expression>(var); }))
      .def(py::init<const Variable &>())
      .def("__abs__", [](const Expression &self) { return abs(self); })
      .def("__str__", &Expression::to_string)
      .def("__repr__",
           [](const Expression &self) {
             return (std::stringstream{} << "<Expression '" << self.to_string() << "'>").str();
           })
      .def("to_string", &Expression::to_string)
      .def("to_smt2_string", &Expression::to_smt2_string)
      .def("Expand", &Expression::Expand)
      .def("Evaluate", [](const Expression &self) { return self.Evaluate().get_d(); })
      .def("Evaluate", [](const Expression &self,
                          const Environment::double_map &env) { return self.Evaluate(Environment{env}).get_d(); })
      .def("EvaluatePartial", [](const Expression &self,
                                 const Environment::double_map &env) { return self.EvaluatePartial(Environment{env}); })
      .def("Substitute",
           [](const Expression &self, const Variable &var, const Expression &e) { return self.Substitute(var, e); })
      // Addition
      .def(py::self + py::self)
      .def(py::self + Variable())
      .def(py::self + double())
      .def(Variable() + py::self)
      .def(double() + py::self)
      .def(py::self += py::self)
      .def(py::self += Variable())
      .def(py::self += double())
      // Subtraction.
      .def(py::self - py::self)
      .def(py::self - Variable())
      .def(py::self - double())
      .def(Variable() - py::self)
      .def(double() - py::self)
      .def(py::self -= py::self)
      .def(py::self -= Variable())
      .def(py::self -= double())
      // Multiplication.
      .def(py::self * py::self)
      .def(py::self * Variable())
      .def(py::self * double())
      .def(Variable() * py::self)
      .def(double() * py::self)
      .def(py::self *= py::self)
      .def(py::self *= Variable())
      .def(py::self *= double())
      // Division.
      .def(py::self / py::self)
      .def(py::self / Variable())
      .def(py::self / double())
      .def(Variable() / py::self)
      .def(double() / py::self)
      .def(py::self /= py::self)
      .def(py::self /= Variable())
      .def(py::self /= double())
      // Pow.
      .def("__pow__", [](const Expression &self, const Expression &other) { return pow(self, other); })
      // TODO(soonho): need to add this to drake-symbolic
      // Unary Plus.
      .def(+py::self)
      // Unary Minus.
      .def(-py::self)
      // LT(<).
      //
      // Note that for `double < Expression` case, the reflected op ('>' in this
      // case) is called. For example, `1 < x * y` will return `x * y > 1`.
      .def(py::self < py::self)
      .def(py::self < Variable())
      .def(py::self < double())
      // LE(<=).
      .def(py::self <= py::self)
      .def(py::self <= Variable())
      .def(py::self <= double())
      // GT(>).
      .def(py::self > py::self)
      .def(py::self > Variable())
      .def(py::self > double())
      // GE(>=).
      .def(py::self >= py::self)
      .def(py::self >= Variable())
      .def(py::self >= double())
      // EQ(==).
      .def(py::self == py::self)
      .def(py::self == Variable())
      .def(py::self == double())
      // NE(!=)
      .def(py::self != py::self)
      .def(py::self != Variable())
      .def(py::self != double())
      .def("Differentiate", &Expression::Differentiate);
}