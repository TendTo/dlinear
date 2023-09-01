/**
 * @file py_extension.cpp
 * @author dlinear
 * @date 26 Aug 2023
 * @copyright 2023 dlinear
 */
#include <pybind11/pybind11.h>
#include <pybind11/operators.h>
#include <pybind11/stl.h>

#include "dlinear/version.h"
#include "dlinear/util/Config.h"
#include "dlinear/libs/gmp.h"
#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/smt2/Driver.h"
#include <spdlog/spdlog.h>
#include <spdlog/fmt/ostr.h>
#include "dlinear/api/api.h"

namespace py = pybind11;

using namespace dlinear;

typedef typename std::unordered_map<Variable, double> ExpressionMap;

PYBIND11_MODULE(_pydlinear, m) {
  m.attr("__version__") = DLINEAR_VERSION_STRING;
  m.doc() = "dlinear python bindings";

  auto MpqArrayClass = py::class_<qsopt_ex::MpqArray>(m, "MpqArray");
  auto FormulaClass = py::class_<Formula>(m, "Formula");
  auto VariableClass = py::class_<Variable>(m, "Variable");
  auto VariableTypeEnum = py::enum_<Variable::Type>(m, "VariableType");
  auto ExpressionClass = py::class_<Expression>(m, "Expression");
  auto VariablesClass = py::class_<Variables>(m, "Variables");
  auto LPSolverEnum = py::enum_<Config::LPSolver>(m, "LPSolver");
  auto SatDefaultPhaseEnum = py::enum_<Config::SatDefaultPhase>(m, "SatDefaultPhase");
  auto ConfigClass = py::class_<Config>(m, "Config");
  auto Smt2DriverClass = py::class_<Smt2Driver>(m, "Smt2Driver");
  auto ContextClass = py::class_<Context>(m, "Context");

  m.def("init_solver", py::overload_cast<const Config &>(&InitSolver), "Initialize solver")
      .def("init_solver", py::overload_cast<Config::LPSolver>(&InitSolver), "Initialize solver")
      .def("de_init_solver", py::overload_cast<const Config &>(&DeInitSolver), "De-initialize solver")
      .def("de_init_solver", py::overload_cast<Config::LPSolver>(&DeInitSolver), "De-initialize solver");

  ContextClass.def(py::init<>())
      .def(py::init<const Config &>());

  Smt2DriverClass.def(py::init<>())
      .def(py::init([](const Config &config) { return Smt2Driver{Context{config}}; }))
      .def("parse_file", &Smt2Driver::parse_file)
      .def("parse_string", &Smt2Driver::parse_string)
      .def("check_sat", &Smt2Driver::CheckSat)
      .def("get_model", &Smt2Driver::GetModel)
      .def_property("trace_scanning", &Smt2Driver::trace_scanning, &Smt2Driver::set_trace_scanning)
      .def_property("trace_parsing", &Smt2Driver::trace_parsing, &Smt2Driver::set_trace_parsing);

  MpqArrayClass.def(py::init<size_t>())
      .def("__len__", &qsopt_ex::MpqArray::size)
      .def("__getitem__", [](const qsopt_ex::MpqArray &self, int i) { return mpq_get_d(self[i]); });

  FormulaClass.def(py::init<const Variable &>())
      .def("GetFreeVariables", &Formula::GetFreeVariables)
      .def("EqualTo", &Formula::EqualTo)
      .def("Evaluate", [](const Formula &self) { return self.Evaluate(); })
//      .def("Evaluate",
//           [](const Formula &self, const Environment::map &env) {
//             Environment e;
//             return self.Evaluate(Environment{env});
//           })
      .def("Substitute",
           [](const Formula &self, const Variable &var, const Expression &e) { return self.Substitute(var, e); })
      .def("to_string", &Formula::to_string)
      .def("__str__", &Formula::to_string)
      .def("__repr__", [](const Formula &self) { return fmt::format("<Formula \"{}\">", self.to_string()); })
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
      .def("__repr__", [](const Variable &self) { return fmt::format("Variable('{}')", self.to_string()); })
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
      .def("__pow__", [](const Variable &self, const Expression &other) { return pow(self, other); }, py::is_operator())
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

  VariableTypeEnum.value("Real", Variable::Type::CONTINUOUS)
      .value("Int", Variable::Type::INTEGER)
      .value("Bool", Variable::Type::BOOLEAN)
      .value("Binary", Variable::Type::BINARY)
      .export_values();

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
      .def("__repr__", [](const Variables &self) { return fmt::format("<Variables \"{}\">", self); })
      .def("to_string", &Variables::to_string)
      .def("__hash__", [](const Variables &self) { return hash_value<Variables>{}(self); })
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
      .def("__iter__",
           [](const Variables &vars) { return py::make_iterator(vars.begin(), vars.end()); },
           py::keep_alive<0, 1>() /* Essential: keep object alive while iterator exists */)
      .def(py::self == py::self)
      .def(py::self < py::self)
      .def(py::self + py::self)
      .def(py::self + Variable())
      .def(Variable() + py::self)
      .def(py::self - py::self)
      .def(py::self - Variable());

  ExpressionClass.def(py::init<>())
      .def(py::init<double>())
      .def(py::init<const Variable &>())
      .def("__abs__", [](const Expression &self) { return abs(self); })
      .def("__str__", &Expression::to_string)
      .def("__repr__", [](const Expression &self) { return fmt::format("<Expression \"{}\">", self.to_string()); })
      .def("to_string", &Expression::to_string)
      .def("Expand", &Expression::Expand)
      .def("Evaluate", [](const Expression &self) { return self.Evaluate().get_d(); })
      .def("Evaluate",
           [](const Expression &self, const Environment::double_map &env) {
             return self.Evaluate(Environment{env}).get_d();
           })
      .def("EvaluatePartial",
           [](const Expression &self, const Environment::double_map &env) {
             return self.EvaluatePartial(Environment{env});
           })
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
          // .def(+py::self)
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

  LPSolverEnum.value("QSOPTEX", Config::LPSolver::QSOPTEX)
      .value("SOPLEX", Config::LPSolver::SOPLEX)
      .export_values();

  SatDefaultPhaseEnum.value("RANDOM_INITIAL_PHASE", Config::SatDefaultPhase::RandomInitialPhase)
      .value("FALSE", Config::SatDefaultPhase::False)
      .value("TRUE", Config::SatDefaultPhase::True)
      .value("JEROS_LOW_WANG", Config::SatDefaultPhase::JeroslowWang)
      .export_values();

  ConfigClass.def(py::init<>())
      .def_property("precision",
                    &Config::precision,
                    [](Config &self, const double prec) { self.mutable_precision() = prec; })
      .def_property("use_polytope",
                    &Config::use_polytope,
                    [](Config &self, const bool use_polytope) { self.mutable_use_polytope() = use_polytope; })
      .def_property("use_polytope_in_forall",
                    &Config::use_polytope_in_forall,
                    [](Config &self, const bool use_polytope_in_forall) {
                      self.mutable_use_polytope_in_forall() = use_polytope_in_forall;
                    })
      .def_property("use_worklist_fixpoint",
                    &Config::use_worklist_fixpoint,
                    [](Config &self, const bool use_worklist_fixpoint) {
                      self.mutable_use_worklist_fixpoint() = use_worklist_fixpoint;
                    })
      .def_property("use_local_optimization",
                    &Config::use_local_optimization,
                    [](Config &self, const bool use_local_optimization) {
                      self.mutable_use_local_optimization() = use_local_optimization;
                    })
      .def_property("nlopt_ftol_rel",
                    &Config::nlopt_ftol_rel,
                    [](Config &self, const bool nlopt_ftol_rel) { self.mutable_nlopt_ftol_rel() = nlopt_ftol_rel; })
      .def_property("nlopt_ftol_abs",
                    &Config::nlopt_ftol_abs,
                    [](Config &self, const bool nlopt_ftol_abs) { self.mutable_nlopt_ftol_abs() = nlopt_ftol_abs; })
      .def_property("nlopt_maxeval",
                    &Config::nlopt_maxeval,
                    [](Config &self, const bool nlopt_maxeval) { self.mutable_nlopt_maxeval() = nlopt_maxeval; })
      .def_property("nlopt_maxtime",
                    &Config::nlopt_maxtime,
                    [](Config &self, const bool nlopt_maxtime) { self.mutable_nlopt_maxtime() = nlopt_maxtime; })
      .def_property("number_of_jobs",
                    &Config::number_of_jobs,
                    [](Config &self, const int number_of_jobs) { self.mutable_number_of_jobs() = number_of_jobs; })
      .def_property("sat_default_phase",
                    &Config::sat_default_phase,
                    [](Config &self, const Config::SatDefaultPhase sat_default_phase) {
                      self.mutable_sat_default_phase() = sat_default_phase;
                    })
      .def_property("random_seed",
                    &Config::random_seed,
                    [](Config &self, const int random_seed) { self.mutable_random_seed() = random_seed; })
      .def_property("debug_scanning",
                    &Config::debug_scanning,
                    [](Config &self, const bool debug_scanning) { self.mutable_debug_scanning() = debug_scanning; })
      .def_property("debug_parsing",
                    &Config::debug_parsing,
                    [](Config &self, const bool debug_parsing) { self.mutable_debug_parsing() = debug_parsing; })
      .def_property("verbose_simplex",
                    &Config::verbose_simplex,
                    [](Config &self, const bool verbose_simplex) { self.mutable_verbose_simplex() = verbose_simplex; })
      .def_property("continuous_output",
                    &Config::continuous_output,
                    [](Config &self, const bool continuous_output) {
                      self.mutable_continuous_output() = continuous_output;
                    })
      .def_property("with_timings",
                    &Config::with_timings,
                    [](Config &self, const bool with_timings) { self.mutable_with_timings() = with_timings; })
      .def_property("produce_models",
                    &Config::produce_models,
                    [](Config &self, const bool produce_models) { self.mutable_produce_models() = produce_models; })
      .def_property("lp_solver",
                    &Config::lp_solver,
                    [](Config &self, const Config::LPSolver lp_solver) { self.mutable_lp_solver() = lp_solver; })
      .def_property("simplex_sat_phase",
                    &Config::simplex_sat_phase,
                    [](Config &self, const int simplex_sat_phase) {
                      self.mutable_simplex_sat_phase() = simplex_sat_phase;
                    })
      .def("__str__", [](const Config &self) { return fmt::format("{}", self); }
      );

}
