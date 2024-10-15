/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Qsopt_ex wrapper.
 *
 * This header includes the Qsopt_ex library and provides a various helpers.
 * Other files in the library should depend on this header instead of the Qsopt_ex library directly.
 * Instead of including <qsopt_ex/Qsopt_ex.h>, include "dlinear/libs/libqsopt_ex.h".
 * In the build files, instead of depending on "@qsopt_ex", depend on "//dlinear/libs:qsopt_ex".
 */
#pragma once

#ifndef DLINEAR_ENABLED_QSOPTEX
#error QSopt_ex is not enabled. Please enable it by adding "--//tools:enable_qsoptex" to the bazel command.
#endif

#include <gmpxx.h>

extern "C" {
#include <qsopt_ex/QSopt_ex.h>  // IWYU pragma: export
}

#include <string>

// These #defines from <qsopt_ex/QSopt_ex.h> cause problems for us
// because they mess with SoPlex's enums.
#undef OPTIMAL
#undef DUAL_INFEASIBLE

namespace dlinear::qsopt_ex {

/**
 * Convert a string to a mpq_class.
 * @param str string representation of a rational number
 * @return pointer to a dynamically allocated mpq_class. Must be freed with delete.
 * @warning The caller is responsible for freeing the returned pointer.
 */
mpq_class *StringToMpqPtr(const std::string &str);
/**
 * Convert a string to a mpq_class.
 * @param str string representation of a rational number
 * @return mpq_class object
 */
mpq_class StringToMpq(const std::string &str);
/**
 * Convert a C-string to a mpq_class.
 * @param str C-string representation of a rational number
 * @return pointer to a dynamically allocated mpq_class. Must be freed with delete.
 * @warning The caller is responsible for freeing the returned pointer.
 */
mpq_class *CStringToMpqPtr(const char str[]);
/**
 * Convert a string to a mpq_class.
 * @param str C-string representation of a rational number
 * @return mpq_class object
 */
mpq_class CStringToMpq(const char str[]);

/**
 * A wrapper around an array of mpq_t elements.
 *
 * It is used to pass around arrays of mpq_t, ensuring they are cleaned up after use.
 * The array is allocated by AllocateMpqArray() and freed by FreeMpqArray().
 */
class MpqArray {
 public:
  /**
   * Construct a new MpqArray object, allocating the array with @p nElements elements.
   * @param nElements The number of elements in the array.
   */
  explicit MpqArray(size_t nElements);
  MpqArray(const MpqArray &) = delete;
  MpqArray(MpqArray &&) = delete;
  MpqArray &operator=(const MpqArray &) = delete;
  MpqArray &operator=(MpqArray &&) = delete;
  /** Destroy the MpqArray object, freeing the array */
  ~MpqArray();
  /**
   * Obtain a constant pointer to the internal array.
   * @return internal mpq_t array as a constant pointer
   */
  explicit operator const mpq_t *() const { return array; }

  /**
   * Obtain a pointer to the internal array.
   * @return internal mpq_t array
   */
  explicit operator mpq_t *() { return array; }

  mpq_t &operator[](const int idx) { return array[idx]; }

  const mpq_t &operator[](const int idx) const { return array[idx]; }

  /** @getter{size, array} */
  [[nodiscard]] size_t size() const { return array ? reinterpret_cast<size_t *>(array)[-1] : 0; }

  /**
   * Resize the array to have @p nElements elements.
   *
   * All the previous elements are lost.
   * @param nElements new  number of elements in the array
   */
  void Resize(size_t nElements);

 private:
  mpq_t *array;  ///< array of mpq_t. It is allocated by AllocateMpqArray() and freed by FreeMpqArray().

  /**
   * Allocate the array with @p nElements elements.
   *
   * The array has a peculiar structure, where the element at index -1 is the size of the array.
   * @param nElements The number of elements in the array.
   */
  void AllocateMpqArray(size_t nElements);

  /** Free the array of mpq_t */
  void FreeMpqArray();
};

void QSXStart();
void QSXFinish();

}  // namespace dlinear::qsopt_ex
