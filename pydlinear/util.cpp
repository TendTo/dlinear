/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#ifndef DLINEAR_PYDLINEAR
#error DLINEAR_PYDLINEAR is not defined. Ensure you are building with the option '--config=pydlinear'
#endif

#include <pybind11/stl.h>

#include "dlinear/libs/libgmp.h"
#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"
#include "pydlinear.h"

namespace py = pybind11;
using namespace dlinear;

void init_util(py::module_ &m) {
  m.attr("LOG_NONE") = -1;
  m.attr("LOG_CRITICAL") = 0;
  m.attr("LOG_ERROR") = 1;
  m.attr("LOG_WARN") = 2;
  m.attr("LOG_INFO") = 3;
  m.attr("LOG_DEBUG") = 4;
  m.attr("LOG_TRACE") = 5;
  m.def("set_verbosity", [](int value) { DLINEAR_LOG_INIT_VERBOSITY(value); });

  py::enum_<Config::LPSolver>(m, "LPSolver")
      .value("QSOPTEX", Config::LPSolver::QSOPTEX)
      .value("SOPLEX", Config::LPSolver::SOPLEX);

  py::enum_<Config::SatDefaultPhase>(m, "SatDefaultPhase")
      .value("RANDOM_INITIAL_PHASE", Config::SatDefaultPhase::RandomInitialPhase)
      .value("FALSE", Config::SatDefaultPhase::False)
      .value("TRUE", Config::SatDefaultPhase::True)
      .value("JEROS_LOW_WANG", Config::SatDefaultPhase::JeroslowWang);

  py::enum_<Config::Format>(m, "Format")
      .value("AUTO", Config::Format::AUTO)
      .value("SMT2", Config::Format::SMT2)
      .value("MPS", Config::Format::MPS);

  py::enum_<Config::SatSolver>(m, "SatSolver")
      .value("PICOSAT", Config::SatSolver::PICOSAT)
      .value("CADICAL", Config::SatSolver::CADICAL);

  py::enum_<Config::PreprocessingRunningFrequency>(m, "PreprocessingRunningFrequency")
      .value("AUTO", Config::PreprocessingRunningFrequency::AUTO)
      .value("NEVER", Config::PreprocessingRunningFrequency::NEVER)
      .value("ON_FIXED", Config::PreprocessingRunningFrequency::ON_FIXED)
      .value("ON_ITERATION", Config::PreprocessingRunningFrequency::ON_ITERATION)
      .value("ALWAYS", Config::PreprocessingRunningFrequency::ALWAYS);

  py::enum_<Config::BoundPropagationType>(m, "BoundPropagationType")
      .value("AUTO", Config::BoundPropagationType::AUTO)
      .value("EQ_BINOMIAL", Config::BoundPropagationType::EQ_BINOMIAL)
      .value("EQ_POLYNOMIAL", Config::BoundPropagationType::EQ_POLYNOMIAL)
      .value("BOUND_POLYNOMIAL", Config::BoundPropagationType::BOUND_POLYNOMIAL);

  py::enum_<Config::LPMode>(m, "LPMode")
      .value("AUTO", Config::LPMode::AUTO)
      .value("PURE_PRECISION_BOOSTING", Config::LPMode::PURE_PRECISION_BOOSTING)
      .value("PURE_ITERATIVE_REFINEMENT", Config::LPMode::PURE_ITERATIVE_REFINEMENT)
      .value("HYBRID", Config::LPMode::HYBRID);

  py::class_<Config>(m, "Config")
      .def(py::init<>())
      .def_static("from_args",
                  [](const std::vector<std::string> &args) {
                    const char **argv = new const char *[args.size()];
                    for (size_t i = 0; i < args.size(); ++i) {
                      argv[i] = const_cast<char *>(args[i].c_str());
                    }
                    ArgParser argparser{};
                    argparser.parse(static_cast<int>(args.size()), argv);
                    delete[] argv;
                    return argparser.toConfig();
                  })
      .def_property("bound_implication_frequency", &Config::bound_implication_frequency,
                    [](Config &self, const Config::PreprocessingRunningFrequency &frequency) {
                      self.m_bound_implication_frequency() = frequency;
                    })
      .def_property("bound_propagation_frequency", &Config::bound_propagation_frequency,
                    [](Config &self, const Config::PreprocessingRunningFrequency &frequency) {
                      self.m_bound_propagation_frequency() = frequency;
                    })
      .def_property(
          "bound_propagation_type", &Config::bound_propagation_type,
          [](Config &self, const Config::BoundPropagationType &type) { self.m_bound_propagation_type() = type; })
      .def_property("csv", &Config::csv, [](Config &self, bool value) { self.m_csv() = value; })
      .def_property("complete", &Config::complete, [](Config &self, bool value) { self.m_complete() = value; })
      .def_property("continuous_output", &Config::continuous_output,
                    [](Config &self, const bool value) { self.m_continuous_output() = value; })
      .def_property("debug_parsing", &Config::debug_parsing,
                    [](Config &self, const bool value) { self.m_debug_parsing() = value; })
      .def_property("debug_scanning", &Config::debug_scanning,
                    [](Config &self, const bool value) { self.m_debug_scanning() = value; })
      .def_property("disable_expansion", &Config::disable_expansion,
                    [](Config &self, const bool value) { self.m_disable_expansion() = value; })
      .def_property("enforce_check_sat", &Config::enforce_check_sat,
                    [](Config &self, const bool value) { self.m_enforce_check_sat() = value; })
      .def_property("filename", &Config::filename,
                    [](Config &self, const std::string &value) { self.m_filename() = value; })
      .def_property("format", &Config::format,
                    [](Config &self, const Config::Format &value) { self.m_format() = value; })
      .def_property("lp_mode", &Config::lp_mode,
                    [](Config &self, const Config::LPMode value) { self.m_lp_mode() = value; })
      .def_property("lp_solver", &Config::lp_solver,
                    [](Config &self, const Config::LPSolver &value) { self.m_lp_solver() = value; })
      .def_property("number_of_jobs", &Config::number_of_jobs,
                    [](Config &self, const int value) { self.m_number_of_jobs() = value; })
      .def_property("onnx_file", &Config::onnx_file,
                    [](Config &self, const std::string &value) { self.m_onnx_file() = value; })
      .def_property("optimize", &Config::optimize, [](Config &self, const bool value) { self.m_optimize() = value; })
      .def_property("precision", &Config::precision, [](Config &self, double value) { self.m_precision() = value; })
      .def_property("produce_model", &Config::produce_models,
                    [](Config &self, const bool value) { self.m_produce_models() = value; })
      .def_property("random_seed", &Config::random_seed, [](Config &self, int value) { self.m_random_seed() = value; })
      .def_property("read_from_stdin", &Config::read_from_stdin,
                    [](Config &self, const bool value) { self.m_read_from_stdin() = value; })
      .def_property("sat_default_phase", &Config::sat_default_phase,
                    [](Config &self, const Config::SatDefaultPhase &value) { self.m_sat_default_phase() = value; })
      .def_property("sat_solver", &Config::sat_solver,
                    [](Config &self, const Config::SatSolver value) { self.m_sat_solver() = value; })
      .def_property("silent", &Config::silent, [](Config &self, bool value) { self.m_silent() = value; })
      .def_property("simplex_sat_phase", &Config::simplex_sat_phase,
                    [](Config &self, const int value) { self.m_simplex_sat_phase() = value; })
      .def_property("skip_check_sat", &Config::skip_check_sat,
                    [](Config &self, const bool value) { self.m_skip_check_sat() = value; })
      .def_property("verbose_dlinear", &Config::verbose_dlinear,
                    [](Config &self, const int value) { self.m_verbose_dlinear() = value; })
      .def_property("verbose_simplex", &Config::verbose_simplex,
                    [](Config &self, const int value) { self.m_verbose_simplex() = value; })
      .def_property("verify", &Config::verify, [](Config &self, const bool value) { self.m_verify() = value; })
      .def_property("with_timings", &Config::with_timings,
                    [](Config &self, const bool value) { self.m_with_timings() = value; })
      .def("__str__", [](const Config &self) { return (std::stringstream() << self).str(); });

  py::class_<Interval>(m, "Interval")
      .def(py::init<const mpq_class &>())
      .def(py::init<const mpq_class &, const mpq_class &>())
      .def("set_empty", &Interval::set_empty)
      .def_property_readonly("lb", [](const Interval &self) { return self.lb().get_d(); })
      .def_property_readonly("ub", [](const Interval &self) { return self.ub().get_d(); })
      .def_property_readonly("diam", [](const Interval &self) { return self.diam().get_d(); })
      .def_property_readonly("is_empty", &Interval::is_empty)
      .def_property_readonly("is_bisectable", &Interval::is_bisectable)
      .def_property_readonly("is_degenerated", &Interval::is_degenerated)
      .def("bisect", &Interval::bisect)
      .def("__eq__", &Interval::operator==)
      .def("__add__", py::overload_cast<const Interval &>(&Interval::operator+=))
      .def("__add__", py::overload_cast<const mpq_class &>(&Interval::operator+=))
      .def("__sub__", py::overload_cast<const Interval &>(&Interval::operator-=))
      .def("__sub__", py::overload_cast<const mpq_class &>(&Interval::operator-=))
      .def("__mul__", py::overload_cast<const Interval &>(&Interval::operator*=))
      .def("__mul__", py::overload_cast<const mpq_class &>(&Interval::operator*=))
      .def("__truediv__", py::overload_cast<const Interval &>(&Interval::operator/=))
      .def("__truediv__", py::overload_cast<const mpq_class &>(&Interval::operator/=))
      .def("__str__", [](const Config &self) { return (std::stringstream() << self).str(); });

  py::class_<Box>(m, "Box")
      .def(py::init<Config::LPSolver>())
      .def(py::init<const std::vector<Variable> &, Config::LPSolver>())
      .def("Add", py::overload_cast<const Variable &>(&Box::Add))
      .def("Add", py::overload_cast<const Variable &, const mpq_class &, const mpq_class &>(&Box::Add))
      .def("__getitem__", py::overload_cast<const Variable &>(&Box::operator[]))
      .def("__setitem__", [](Box &self, const Variable &var, const Interval &iv) { self[var] = iv; })
      .def_property_readonly("size", &Box::size)
      .def_property_readonly("empty", &Box::empty)
      .def_property_readonly("lp_solver", &Box::lp_solver)
      .def_property_readonly("variables", &Box::variables)
      .def("__len__", &Box::size)
      .def("__contains__", &Box::has_variable)
      .def("__str__", [](const Config &self) { return (std::stringstream() << self).str(); });
}