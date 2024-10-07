/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#ifndef DLINEAR_PYDLINEAR
#error DLINEAR_PYDLINEAR is not defined. Ensure you are building with the option '--config=pydlinear'
#endif

#include <pybind11/operators.h>

#include "dlinear/solver/SmtSolver.h"
#include "dlinear/solver/SmtSolverOutput.h"
#include "pydlinear.h"

namespace py = pybind11;
using namespace dlinear;

void init_solver(py::module_ &m) {
  py::enum_<SmtResult>(m, "SmtResult")
      .value("SAT", SmtResult::SAT)
      .value("DELTA_SAT", SmtResult::DELTA_SAT)
      .value("UNSAT", SmtResult::UNSAT)
      .value("ERROR", SmtResult::ERROR)
      .value("UNKNOWN", SmtResult::UNKNOWN)
      .value("UNSOLVED", SmtResult::UNSOLVED)
      .value("SKIP_SAT", SmtResult::SKIP_SAT);

  py::class_<SmtSolverOutput>(m, "SmtSolverOutput")
      .def("matched_expectation", &SmtSolverOutput::matches_expectation)
      .def_property_readonly("result", [](const SmtSolverOutput &self) { return self.result; })
      .def_property_readonly("precision", [](const SmtSolverOutput &self) { return self.precision.get_d(); })
      .def_property_readonly("precision_upper_bound", &SmtSolverOutput::precision_upper_bound)
      .def_property_readonly("actual_precision",
                             [](const SmtSolverOutput &self) { return self.actual_precision.get_d(); })
      .def_property_readonly("lower_bound", [](const SmtSolverOutput &self) { return self.lower_bound.get_d(); })
      .def_property_readonly("upper_bound", [](const SmtSolverOutput &self) { return self.upper_bound.get_d(); })
      .def_property_readonly("model", [](const SmtSolverOutput &self) { return self.model; })
      .def_property_readonly("with_timings", [](const SmtSolverOutput &self) { return self.with_timings; })
      .def_property_readonly("produce_models", [](const SmtSolverOutput &self) { return self.produce_models; })
      .def_property_readonly("n_assertions", [](const SmtSolverOutput &self) { return self.n_assertions; })
      .def_property_readonly("is_sat", &SmtSolverOutput::is_sat)
      .def_property_readonly("exit_code", &SmtSolverOutput::exit_code)
      .def_property_readonly("complete_model", [](const SmtSolverOutput &self) { return self.complete_model; })
      .def_property_readonly("ite_time", [](const SmtSolverOutput &self) { return self.ite_stats.timer().seconds(); })
      .def_property_readonly("sat_time", [](const SmtSolverOutput &self) { return self.sat_stats.timer().seconds(); })
      .def_property_readonly("parser_time",
                             [](const SmtSolverOutput &self) { return self.parser_stats.timer().seconds(); })
      .def_property_readonly("cnfizer_time",
                             [](const SmtSolverOutput &self) { return self.cnfizer_stats.timer().seconds(); })
      .def_property_readonly("theory_time",
                             [](const SmtSolverOutput &self) { return self.theory_stats.timer().seconds(); })
      .def_property_readonly("preprocessor_time",
                             [](const SmtSolverOutput &self) { return self.preprocessor_stats.timer().seconds(); })
      .def_property_readonly(
          "predicate_abstractor",
          [](const SmtSolverOutput &self) { return self.predicate_abstractor_stats.timer().seconds(); })
      .def("__str__", [](const SmtSolverOutput &self) { return (std::stringstream() << self).str(); });

  py::class_<SmtSolver>(m, "SmtSolver")
      .def(py::init<>())
      .def(py::init<Config>())
      .def(py::init<const std::string &>())
      .def("Assert", &SmtSolver::Assert, py::arg("assertion"))
      .def("CheckSat", &SmtSolver::CheckSat)
      .def("GetInfo", &SmtSolver::GetInfo, py::arg("key"))
      .def("GetOption", &SmtSolver::GetOption, py::arg("key"))
      .def("GetExpected", &SmtSolver::GetExpected)
      .def("Verify", &SmtSolver::Verify)
      .def("Parse", py::overload_cast<>(&SmtSolver::Parse))
      .def("Parse", py::overload_cast<const std::string &>(&SmtSolver::Parse), py::arg("filename"));
}