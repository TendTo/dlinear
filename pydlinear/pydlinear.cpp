/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#ifndef DLINEAR_PYDLINEAR
#error DLINEAR_PYDLINEAR is not defined. Ensure you are building with the option '--config=pydlinear'
#endif

#include "pydlinear.h"

#include "dlinear/libs/libgmp.h"
#include "dlinear/version.h"

namespace py = pybind11;

PYBIND11_MODULE(_pydlinear, m) {
  //  init_lib(m);
  init_symbolic(m);
  init_util(m);
  init_solver(m);

  m.doc() = "delta-complete SMT solver for linear theories over the reals";
#ifdef DLINEAR_VERSION_STRING
  m.attr("__version__") = DLINEAR_VERSION_STRING;
#else
#error "DLINEAR_VERSION_STRING is not defined"
#endif
}
