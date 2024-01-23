/**
 * @file py_extension.cpp
 * @author dlinear
 * @date 26 Aug 2023
 * @copyright 2023 dlinear
 */
#include <pybind11/operators.h>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include <spdlog/spdlog.h>

#ifndef DLINEAR_PYDLINEAR
#define DLINEAR_PYDLINEAR
#endif

#include "dlinear/api/api.h"
#include "dlinear/libs/gmp.h"
#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/solver/Solver.h"
#include "dlinear/solver/SolverOutput.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/Infinity.h"
#include "dlinear/util/logging.h"
#include "dlinear/version.h"

namespace py = pybind11;

using namespace dlinear;

typedef typename std::unordered_map<Variable, double> ExpressionMap;

namespace PYBIND11_NAMESPACE {
namespace detail {
template <>
struct type_caster<mpq_class> {
 public:
  /**
   * This macro establishes the name 'inty' in
   * function signatures and declares a local variable
   * 'value' of type inty
   */
  PYBIND11_TYPE_CASTER(mpq_class, const_name("mpq_class"));

  /**
   * Conversion part 1 (Python->C++): convert a PyObject into a mpq_class
   * instance or return false upon failure. The second argument
   * indicates whether implicit conversions should be applied.
   */
  bool load(handle src, bool) {
    /* Extract PyObject from handle */
    PyObject *source = src.ptr();
    /* Try converting into a Python float value */
    PyObject *tmp = PyNumber_Float(source);
    if (!tmp) return false;
    /* Now try to convert into a C++ mpq_class */
    mpq_class value{PyFloat_AsDouble(tmp)};
    Py_DECREF(tmp);
    /* Ensure return code was OK (to avoid out-of-range errors etc) */
    return !PyErr_Occurred();
  }

  /**
   * Conversion part 2 (C++ -> Python): convert an mpq_class instance into
   * a Python object. The second and third arguments are used to
   * indicate the return value policy and parent object (for
   * ``return_value_policy::reference_internal``) and are generally
   * ignored by implicit casters.
   */
  static handle cast(const mpq_class &src, return_value_policy /* policy */, handle /* parent */) {
    return PyFloat_FromDouble(src.get_d());
  }
};
}  // namespace detail
}  // namespace PYBIND11_NAMESPACE

PYBIND11_MODULE(_pydlinear, m) {
  m.attr("__version__") = DLINEAR_VERSION_STRING;
  m.doc() = "dlinear python bindings";

  m.def(
      "set_verbosity", [](int level) { DLINEAR_LOG_INIT_VERBOSITY(level); },
      "Set the verbosity level of dlinear.\n"
      "-1: off\n"
      "0: critical\n"
      "1: error\n"
      "2: warn\n"
      "3: info\n"
      "4: debug\n"
      "5: trace\n");

  auto MpqArrayClass = py::class_<qsopt_ex::MpqArray>(m, "MpqArray");
  auto FormulaClass = py::class_<Formula>(m, "Formula");
  auto VariableClass = py::class_<Variable>(m, "Variable");
  auto VariableTypeEnum = py::enum_<Variable::Type>(m, "VariableType");
  auto ExpressionClass = py::class_<Expression>(m, "Expression");
  auto VariablesClass = py::class_<Variables>(m, "Variables");
  auto LPSolverEnum = py::enum_<Config::LPSolver>(m, "LPSolver");
  auto SatDefaultPhaseEnum = py::enum_<Config::SatDefaultPhase>(m, "SatDefaultPhase");
  auto FormatEnum = py::enum_<Config::Format>(m, "Format");
  auto ConfigClass = py::class_<Config>(m, "Config");
  auto SolverClass = py::class_<Solver>(m, "Solver");
  auto ContextClass = py::class_<Context>(m, "Context");
  auto SolverOutputClass = py::class_<SolverOutput>(m, "SolverOutput");
  auto BoxClass = py::class_<Box>(m, "Box");
  auto BoxIntervalClass = py::class_<Box::Interval>(m, "Interval");

  SolverClass.def(py::init<>())
      .def(py::init<const Config &>())
      .def(py::init<const std::string &>())
      .def("__enter__", &Solver::Enter)
      .def("__exit__", [](Solver &self, py::object, py::object, py::object) { self.Exit(); })
      .def("CheckSat", &Solver::CheckSat);

  SolverOutputClass.def_property_readonly("result", &SolverOutput::m_result)
      .def_property_readonly("actual_precision", &SolverOutput::m_actual_precision)
      .def_property_readonly("lower_bound", &SolverOutput::m_lower_bound)
      .def_property_readonly("upper_bound", &SolverOutput::m_upper_bound)
      .def_property_readonly("model", &SolverOutput::m_model)
      .def_property_readonly("with_timings", &SolverOutput::with_timings)
      .def_property_readonly("produce_models", &SolverOutput::produce_models)
      .def_property_readonly("n_assertions", &SolverOutput::n_assertions)
      .def_property_readonly("is_sat", &SolverOutput::is_sat)
      .def("__str__", [](const SolverOutput &self) { return (std::stringstream() << self).str(); });

  ContextClass.def(py::init<>()).def(py::init<const Config &>());

  MpqArrayClass.def(py::init<size_t>())
      .def("__len__", &qsopt_ex::MpqArray::size)
      .def("__getitem__", [](const qsopt_ex::MpqArray &self, int i) { return mpq_get_d(self[i]); });

  FormulaClass.def(py::init<const Variable &>())
      .def("GetFreeVariables", &Formula::GetFreeVariables)
      .def("EqualTo", &Formula::EqualTo)
      .def("Evaluate", [](const Formula &self) { return self.Evaluate(); })
      .def("Substitute",
           [](const Formula &self, const Variable &var, const Expression &e) { return self.Substitute(var, e); })
      .def("to_string", &Formula::to_string)
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
      .def("__repr__",
           [](const Variables &self) {
             return (std::stringstream{} << "<Variables '" << self.to_string() << "'>").str();
           })
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
      .def(py::init<>([](double b) {
        if (Infinity::IsInitialized()) return std::make_unique<Expression>(b);
        throw std::runtime_error{"Infinity is not initialized. Please use this class inside a `with Solver`"};
      }))
      .def(py::init<>([](const Variable &var) {
        if (Infinity::IsInitialized()) return std::make_unique<Expression>(var);
        throw std::runtime_error{"Infinity is not initialized. Please use this class inside a `with Solver`"};
      }))
      .def(py::init<const Variable &>())
      .def("__abs__", [](const Expression &self) { return abs(self); })
      .def("__str__", &Expression::to_string)
      .def("__repr__",
           [](const Expression &self) {
             return (std::stringstream{} << "<Expression '" << self.to_string() << "'>").str();
           })
      .def("to_string", &Expression::to_string)
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

  LPSolverEnum.value("QSOPTEX", Config::LPSolver::QSOPTEX).value("SOPLEX", Config::LPSolver::SOPLEX).export_values();

  SatDefaultPhaseEnum.value("RANDOM_INITIAL_PHASE", Config::SatDefaultPhase::RandomInitialPhase)
      .value("FALSE", Config::SatDefaultPhase::False)
      .value("TRUE", Config::SatDefaultPhase::True)
      .value("JEROS_LOW_WANG", Config::SatDefaultPhase::JeroslowWang)
      .export_values();

  FormatEnum.value("AUTO", Config::Format::AUTO)
      .value("SMT2", Config::Format::SMT2)
      .value("MPS", Config::Format::MPS)
      .export_values();

  BoxIntervalClass.def(py::init<>())
      .def(py::init<double, double>())
      .def(py::init<double>())
      .def(py::self == py::self)
      .def(py::self != py::self)
      .def("__str__",
           [](const Box::Interval &self) { return (std::stringstream{} << "<Interval '" << self << "'>").str(); })
      .def("__repr__",
           [](const Box::Interval &self) {
             return (std::stringstream{} << "<Interval [" << self.lb() << ", " << self.ub() << "]>").str();
           })
      .def("is_empty", &Box::Interval::is_empty)
      .def("set_empty", &Box::Interval::set_empty)
      .def("lb", &Box::Interval::lb)
      .def("ub", &Box::Interval::ub)
      .def("mid", &Box::Interval::mid)
      .def("diam", &Box::Interval::diam)
      .def("is_degenerated", &Box::Interval::is_degenerated)
      .def("is_bisectable", &Box::Interval::is_bisectable)
      .def("bisect", &Box::Interval::bisect);

  BoxClass.def(py::init<const std::vector<Variable> &>())
      .def("Add", py::overload_cast<const Variable &>(&Box::Add))
      .def("empty", &Box::empty)
      .def("set_empty", &Box::set_empty)
      .def("size", &Box::size)
      .def("__setitem__", [](Box &self, const Variable &var, const Box::Interval &i) { self[var] = i; })
      .def("__setitem__", [](Box &self, const int idx, const Box::Interval &i) { self[idx] = i; })
      .def("__getitem__", [](const Box &self, const Variable &var) { return self[var]; })
      .def("__getitem__", [](const Box &self, const int idx) { return self[idx]; })
      .def("__repr__", [](const Box &self) { return fmt::format("<Box \"{}\">", self); })
      .def("__len__", &Box::size)
      .def("__delitem__",
           [](const Box &, const Variable &) { throw std::runtime_error{"Box class does not allow deleting an item"}; })
      .def("clear", [](const Box &) { throw std::runtime_error{"Box class does not support the 'clear' operation"}; })
      .def("has_key", [](const Box &self, const Variable &var) { return self.has_variable(var); })
      .def("keys", [](const Box &self) { return self.variables(); })
      .def("values",
           [](const Box &self) {
             std::vector<Box::Interval> ret{static_cast<size_t>(self.size())};
             for (const Box::Interval &iv : self.interval_vector()) ret.push_back(iv);
             return ret;
           })
      .def("items",
           [](const Box &self) {
             const std::vector<Variable> &vars{self.variables()};
             const Box::IntervalVector &iv{self.interval_vector()};
             std::vector<std::pair<Variable, Box::Interval>> ret;
             ret.reserve(iv.size());
             for (std::size_t i = 0; i < iv.size(); ++i) ret.emplace_back(vars[i], iv[i]);
             return ret;
           })
      .def("variable", &Box::variable)
      .def("index", &Box::index)
      .def("MaxDiam", &Box::MaxDiam)
      .def("bisect", [](const Box &self, const int i) { return self.bisect(i); })
      .def("bisect", [](const Box &self, const Variable &var) { return self.bisect(var); })
      .def(py::self == py::self)
      .def(py::self != py::self)
      .def("__str__", [](const Box &self) { return (std::stringstream{} << "<Box '" << self << "'>").str(); })
      .def("set", [](Box &self, const Box &b) { return self = b; });

  ConfigClass.def(py::init<>())
      .def_static("from_command_line",
                  [](std::vector<std::string> args) {
                    const char *argv[args.size()];
                    for (size_t i = 0; i < args.size(); ++i) {
                      argv[i] = const_cast<char *>(args[i].c_str());
                    }
                    ArgParser argparser{};
                    argparser.parse(args.size(), argv);
                    return argparser.toConfig();
                  })
      .def_property(
          "continuous_output", &Config::continuous_output,
          [](Config &self, const bool continuous_output) { self.m_continuous_output() = continuous_output; })
      .def_property("debug_parsing", &Config::debug_parsing,
                    [](Config &self, const bool debug_parsing) { self.m_debug_parsing() = debug_parsing; })
      .def_property("debug_scanning", &Config::debug_scanning,
                    [](Config &self, const bool debug_scanning) { self.m_debug_scanning() = debug_scanning; })
      .def_property("filename", &Config::filename,
                    [](Config &self, const std::string &filename) { self.m_filename() = filename; })
      .def_property("format", &Config::format,
                    [](Config &self, const Config::Format &format) { self.m_format() = format; })
      .def_property("lp_solver", &Config::lp_solver,
                    [](Config &self, const Config::LPSolver lp_solver) { self.m_lp_solver() = lp_solver; })
      .def_property("nlopt_ftol_abs", &Config::nlopt_ftol_abs,
                    [](Config &self, const bool nlopt_ftol_abs) { self.m_nlopt_ftol_abs() = nlopt_ftol_abs; })
      .def_property("nlopt_ftol_rel", &Config::nlopt_ftol_rel,
                    [](Config &self, const bool nlopt_ftol_rel) { self.m_nlopt_ftol_rel() = nlopt_ftol_rel; })
      .def_property("nlopt_maxeval", &Config::nlopt_maxeval,
                    [](Config &self, const bool nlopt_maxeval) { self.m_nlopt_maxeval() = nlopt_maxeval; })
      .def_property("nlopt_maxtime", &Config::nlopt_maxtime,
                    [](Config &self, const bool nlopt_maxtime) { self.m_nlopt_maxtime() = nlopt_maxtime; })
      .def_property("number_of_jobs", &Config::number_of_jobs,
                    [](Config &self, const int number_of_jobs) { self.m_number_of_jobs() = number_of_jobs; })
      .def_property("precision", &Config::precision,
                    [](Config &self, const double prec) { self.m_precision() = prec; })
      .def_property("produce_models", &Config::produce_models,
                    [](Config &self, const bool produce_models) { self.m_produce_models() = produce_models; })
      .def_property("random_seed", &Config::random_seed,
                    [](Config &self, const int random_seed) { self.m_random_seed() = random_seed; })
      .def_property("read_from_stdin", &Config::read_from_stdin,
                    [](Config &self, const bool read_from_stdin) { self.m_read_from_stdin() = read_from_stdin; })
      .def_property("sat_default_phase", &Config::sat_default_phase,
                    [](Config &self, const Config::SatDefaultPhase sat_default_phase) {
                      self.m_sat_default_phase() = sat_default_phase;
                    })
      .def_property("silent", &Config::silent, [](Config &self, const bool silent) { self.m_silent() = silent; })
      .def_property(
          "simplex_sat_phase", &Config::simplex_sat_phase,
          [](Config &self, const int simplex_sat_phase) { self.m_simplex_sat_phase() = simplex_sat_phase; })
      .def_property("skip_check_sat", &Config::skip_check_sat,
                    [](Config &self, const bool skip_check_sat) { self.m_skip_check_sat() = skip_check_sat; })
      .def_property("use_local_optimization", &Config::use_local_optimization,
                    [](Config &self, const bool use_local_optimization) {
                      self.m_use_local_optimization() = use_local_optimization;
                    })
      .def_property("use_polytope", &Config::use_polytope,
                    [](Config &self, const bool use_polytope) { self.m_use_polytope() = use_polytope; })
      .def_property("use_polytope_in_forall", &Config::use_polytope_in_forall,
                    [](Config &self, const bool use_polytope_in_forall) {
                      self.m_use_polytope_in_forall() = use_polytope_in_forall;
                    })
      .def_property("use_worklist_fixpoint", &Config::use_worklist_fixpoint,
                    [](Config &self, const bool use_worklist_fixpoint) {
                      self.m_use_worklist_fixpoint() = use_worklist_fixpoint;
                    })
      .def_property("verbose_dlinear", &Config::verbose_dlinear,
                    [](Config &self, const int verbose_dlinear) { self.m_verbose_dlinear() = verbose_dlinear; })
      .def_property("verbose_simplex", &Config::verbose_simplex,
                    [](Config &self, const int verbose_simplex) { self.m_verbose_simplex() = verbose_simplex; })
      .def_property("with_timings", &Config::with_timings,
                    [](Config &self, const bool with_timings) { self.m_with_timings() = with_timings; })
      .def("__str__", [](const Config &self) { return (std::stringstream() << self).str(); });
}
