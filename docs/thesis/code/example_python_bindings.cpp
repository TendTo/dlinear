#include <pybind11/pybind11.h>
#include <pybind11/operators.h>
#include "dlinear/..."

using namespace dlinear;
namespace py = pybind11;

PYBIND11_MODULE(_pydlinear, m) {
  m.attr("__version__") = DLINEAR_VERSION_STRING;
  m.doc() = "dlinear Python bindings";

  auto FormulaC = py::class_<Formula>(m, "Formula");
  auto LPSolverE = py::enum_<Config::LPSolver>(m, "LPSolver");

  m.def("init_solver", py::overload_cast<const Config &>(&InitSolver), "Initialize solver")
    .def("init_solver", py::overload_cast<Config::LPSolver>(&InitSolver), "Initialize solver");

  FormulaC.def(py::init<const Variable &>())
      .def("GetFreeVariables", &Formula::GetFreeVariables)
      .def("__str__", &Formula::to_string)
      .def("__eq__", [](const Formula &s, const Formula &o) 
        { return s.EqualTo(o); })
      .def("__ne__", [](const Formula &s, const Formula &o) 
        { return !s.EqualTo(o); })
      .def("__hash__", [](const Formula &s) 
        { return std::hash<Formula>{}(s); })
      .def("__bool__", [](const Formula &f) 
        { return f.Evaluate(); })
      .def(py::self == Variable()) // EQ(==).
      .def(py::self != Variable()) // NE(!=).
      .def_static("TRUE", &Formula::True)
      .def_static("FALSE", &Formula::False);

 LPSolverE.value("QSOPTEX", Config::LPSolver::QSOPTEX)
      .value("SOPLEX", Config::LPSolver::SOPLEX)
      .export_values();
}
