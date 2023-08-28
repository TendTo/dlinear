/**
 * @file py_extension.cpp
 * @author dlinear
 * @date 26 Aug 2023
 * @copyright 2023 dlinear
 */
#include <pybind11/pybind11.h>
#include <pybind11/operators.h>

#include "dlinear/version.h"
#include "dlinear/util/Config.h"
#include "dlinear/libs/gmp.h"
#include "dlinear/libs/qsopt_ex.h"
#include "dlinear/symbolic/symbolic.h"

namespace py = pybind11;

using namespace dlinear;

using std::pair;
using std::vector;

PYBIND11_MODULE(_pydlinear, m) {
  m.attr("__version__") = DLINEAR_VERSION_STRING;
  m.doc() = "dlinear python bindings";

  m.def("gmp_floor", [](double v) {
        return gmp::floor(v).get_d();
      })
      .def("gmp_ceil", [](double v) {
        return gmp::ceil(v).get_d();
      });

  m.def("create_mpq_problem", []() {
    return mpq_QScreate_prob(nullptr, QS_MIN);
  });

  py::class_<qsopt_ex::MpqArray>(m, "MpqArray")
      .def(py::init<size_t>())
      .def("__len__", &qsopt_ex::MpqArray::size)
      .def("__getitem__", [](const qsopt_ex::MpqArray &self, int i) { return mpq_get_d(self[i]); });

  py::class_<Formula>(m, "Formula")
      .def(py::init<const Variable &>())
      .def("GetFreeVariables", &Formula::GetFreeVariables)
      .def("EqualTo", &Formula::EqualTo)
      .def("Evaluate", [](const Formula &self) { return self.Evaluate(); })
      .def("Evaluate",
           [](const Formula &self, const Environment::map &env) {
             Environment e;
             return self.Evaluate(Environment{env});
           })
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

  py::enum_<Variable::Type>(m, "VariableType")
      .value("Real", Variable::Type::CONTINUOUS)
      .value("Int", Variable::Type::INTEGER)
      .value("Bool", Variable::Type::BOOLEAN)
      .value("Binary", Variable::Type::BINARY)
      .export_values();

  py::class_<Variables>(m, "Variables")
      .def(py::init<>())
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
             return fmt::format("<Variables \"{}\">", self);
           })
      .def("to_string", &Variables::to_string)
      .def("__hash__",
           [](const Variables &self) { return hash_value<Variables>{}(self); })
      .def("insert",
           [](Variables &self, const Variable &var) { self.insert(var); })
      .def("insert",
           [](Variables &self, const Variables &vars) { self.insert(vars); })
      .def("erase",
           [](Variables &self, const Variable &var) { return self.erase(var); })
      .def("erase", [](Variables &self,
                       const Variables &vars) { return self.erase(vars); })
      .def("include", &Variables::include)
      .def("__contains__", &Variables::include)
      .def("IsSubsetOf", &Variables::IsSubsetOf)
      .def("IsSupersetOf", &Variables::IsSupersetOf)
      .def("IsStrictSubsetOf", &Variables::IsStrictSubsetOf)
      .def("IsStrictSupersetOf", &Variables::IsStrictSupersetOf)
      .def(
          "__iter__",
          [](const Variables &vars) {
            return py::make_iterator(vars.begin(), vars.end());
          },
          py::keep_alive<
              0, 1>() /* Essential: keep object alive while iterator exists */)
      .def(py::self == py::self)
      .def(py::self < py::self)
      .def(py::self + py::self)
      .def(py::self + Variable())
      .def(Variable() + py::self)
      .def(py::self - py::self)
      .def(py::self - Variable());

  m.def("intersect", [](const Variables &vars1, const Variables &vars2) {
    return intersect(vars1, vars2);
  });

  py::class_<Expression>(m, "Expression")
      .def(py::init<>())
      .def(py::init<double>())
      .def(py::init<const Variable &>())
      .def("__abs__", [](const Expression &self) { return abs(self); })
      .def("__str__", &Expression::to_string)
      .def("__repr__",
           [](const Expression &self) {
             return fmt::format("<Expression \"{}\">", self.to_string());
           })
      .def("to_string", &Expression::to_string)
      .def("Expand", &Expression::Expand)
      .def("Evaluate", [](const Expression &self) { return self.Evaluate(); })
      .def("Evaluate",
           [](const Expression &self, const Environment::map &env) {
             Environment e;
             return self.Evaluate(Environment{env});
           })
      .def("EvaluatePartial",
           [](const Expression &self, const Environment::map &env) {
             return self.EvaluatePartial(Environment{env});
           })
      .def("Substitute",
           [](const Expression &self, const Variable &var,
              const Expression &e) { return self.Substitute(var, e); })
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
      .def("__pow__", [](const Expression &self,
                         const Expression &other) { return pow(self, other); })
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

  py::enum_<Config::LPSolver>(m, "LPSolver")
      .value("QSOPTEX", Config::LPSolver::QSOPTEX)
      .value("SOPLEX", Config::LPSolver::SOPLEX)
      .export_values();

  py::enum_<Config::SatDefaultPhase>(m, "SatDefaultPhase")
      .value("RANDOM_INITIAL_PHASE", Config::SatDefaultPhase::RandomInitialPhase)
      .value("FALSE", Config::SatDefaultPhase::False)
      .value("TRUE", Config::SatDefaultPhase::True)
      .value("JEROS_LOW_WANG", Config::SatDefaultPhase::JeroslowWang)
      .export_values();

  py::class_<Config>(m, "Config")
      .def(py::init<>())
      .def_property("precision", &Config::precision,
                    [](Config &self, const double prec) {
                      self.mutable_precision() = prec;
                    })
      .def_property("use_polytope", &Config::use_polytope,
                    [](Config &self, const bool use_polytope) {
                      self.mutable_use_polytope() = use_polytope;
                    })
      .def_property("use_polytope_in_forall", &Config::use_polytope_in_forall,
                    [](Config &self, const bool use_polytope_in_forall) {
                      self.mutable_use_polytope_in_forall() = use_polytope_in_forall;
                    })
      .def_property("use_worklist_fixpoint", &Config::use_worklist_fixpoint,
                    [](Config &self, const bool use_worklist_fixpoint) {
                      self.mutable_use_worklist_fixpoint() = use_worklist_fixpoint;
                    })
      .def_property("use_local_optimization", &Config::use_local_optimization,
                    [](Config &self, const bool use_local_optimization) {
                      self.mutable_use_local_optimization() = use_local_optimization;
                    })
      .def_property("nlopt_ftol_rel", &Config::nlopt_ftol_rel,
                    [](Config &self, const bool nlopt_ftol_rel) {
                      self.mutable_nlopt_ftol_rel() = nlopt_ftol_rel;
                    })
      .def_property("nlopt_ftol_abs", &Config::nlopt_ftol_abs,
                    [](Config &self, const bool nlopt_ftol_abs) {
                      self.mutable_nlopt_ftol_abs() = nlopt_ftol_abs;
                    })
      .def_property("nlopt_maxeval", &Config::nlopt_maxeval,
                    [](Config &self, const bool nlopt_maxeval) {
                      self.mutable_nlopt_maxeval() = nlopt_maxeval;
                    })
      .def_property("nlopt_maxtime", &Config::nlopt_maxtime,
                    [](Config &self, const bool nlopt_maxtime) {
                      self.mutable_nlopt_maxtime() = nlopt_maxtime;
                    })
      .def_property("number_of_jobs", &Config::number_of_jobs,
                    [](Config &self, const int number_of_jobs) {
                      self.mutable_number_of_jobs() = number_of_jobs;
                    })
      .def_property("sat_default_phase", &Config::sat_default_phase,
                    [](Config &self, const Config::SatDefaultPhase sat_default_phase) {
                      self.mutable_sat_default_phase() = sat_default_phase;
                    })
      .def_property("random_seed", &Config::random_seed,
                    [](Config &self, const int random_seed) {
                      self.mutable_random_seed() = random_seed;
                    })
      .def_property("debug_scanning", &Config::debug_scanning,
                    [](Config &self, const bool debug_scanning) {
                      self.mutable_debug_scanning() = debug_scanning;
                    })
      .def_property("debug_parsing", &Config::debug_parsing,
                    [](Config &self, const bool debug_parsing) {
                      self.mutable_debug_parsing() = debug_parsing;
                    })
      .def_property("verbose_simplex", &Config::verbose_simplex,
                    [](Config &self, const bool verbose_simplex) {
                      self.mutable_verbose_simplex() = verbose_simplex;
                    })
      .def_property("continuous_output", &Config::continuous_output,
                    [](Config &self, const bool continuous_output) {
                      self.mutable_continuous_output() = continuous_output;
                    })
      .def_property("with_timings", &Config::with_timings,
                    [](Config &self, const bool with_timings) {
                      self.mutable_with_timings() = with_timings;
                    })
      .def_property("produce_models", &Config::produce_models,
                    [](Config &self, const bool produce_models) {
                      self.mutable_produce_models() = produce_models;
                    })
      .def_property("lp_solver", &Config::lp_solver,
                    [](Config &self, const Config::LPSolver lp_solver) {
                      self.mutable_lp_solver() = lp_solver;
                    })
      .def_property("simplex_sat_phase", &Config::simplex_sat_phase,
                    [](Config &self, const int simplex_sat_phase) {
                      self.mutable_simplex_sat_phase() = simplex_sat_phase;
                    })
      .def("__str__", [](const Config &self) { return fmt::format("{}", self); }
      );
}
