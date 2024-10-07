/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#ifndef DLINEAR_PYDLINEAR
#error DLINEAR_PYDLINEAR is not defined. Ensure you are building with the option '--config=pydlinear'
#endif

#include <pybind11/pybind11.h>

#include <sstream>

#define STRINGIFY(x) #x
#define MACRO_STRINGIFY(x) STRINGIFY(x)
#define REPR_LAMBDA(class_name) [](const class_name &o) { return (std::stringstream{} << o).str(); }

void init_util(pybind11::module_ &);
void init_symbolic(pybind11::module_ &);
void init_solver(pybind11::module_ &);
