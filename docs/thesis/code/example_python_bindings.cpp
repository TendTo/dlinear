#include <pybind11/pybind11.h>
#include <pybind11/operators.h>

#define DLINEAR_PYDLINEAR

#include "dlinear/..."

using namespace dlinear;
namespace py = pybind11;

PYBIND11_MODULE(_pydlinear, m) {
  m.attr("__version__") = DLINEAR_VERSION_STRING;
  m.doc() = "dlinear Python bindings";

  auto SolverC = py::class_<Formula>(m, "Formula");
  auto LPSolverE = py::enum_<Config::LPSolver>(m, "LPSolver");

  SolverC.def(py::init<>())
      .def(py::init<const Config &>())
      .def(py::init<const std::string &>())
      .def("__enter__", &Solver::Enter)
      .def("__exit__", [](Solver &self, py::object,
                          py::object, py::object)
        { self.Exit(); })
      .def("CheckSat", &Solver::CheckSat);

 LPSolverE.value("QSOPTEX", Config::LPSolver::QSOPTEX)
      .value("SOPLEX", Config::LPSolver::SOPLEX)
      .export_values();
}
