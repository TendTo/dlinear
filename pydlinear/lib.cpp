/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#ifndef DLINEAR_PYDLINEAR
#error DLINEAR_PYDLINEAR is not defined. Ensure you are building with the option '--config=pydlinear'
#endif

#include "dlinear/libs/libgmp.h"
#include "pydlinear.h"

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
    value = PyFloat_AsDouble(tmp);
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
