/**
 * @file qsopt_ex.h
 * @author dlinear
 * @date 10 Aug 2023
 * @copyright 2023 dlinear
 * Qsopt_ex wrapper.
 *
 * This header includes the Qsopt_ex library and provides a various helpers.
 * Other files in the library should depend on this header instead of the Qsopt_ex library directly.
 * Instead of including <qsopt_ex/Qsopt_ex.h>, include "dlinear/libs/qsopt_ex.h".
 * In the build files, instead of depending on "@qsopt_ex", depend on "//dlinear/libs:qsopt_ex".
 */

#ifndef DLINEAR5_DLINEAR_LIBS_QSOPT_EX_H_
#define DLINEAR5_DLINEAR_LIBS_QSOPT_EX_H_

#include <gmpxx.h>

extern "C" {
#include <qsopt_ex/QSopt_ex.h>
}

#include <string>

// These #defines from <qsopt_ex/QSopt_ex.h> cause problems for us
#undef OPTIMAL
#undef DUAL_INFEASIBLE

using std::string;

namespace dlinear::qsopt_ex {

mpq_class *StringToMpqPtr(const std::string &str);
mpq_class StringToMpq(const std::string &str);

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
   *
   * @param nElements The number of elements in the array.
   */
  explicit MpqArray(size_t nElements);
  /** Destroy the MpqArray object, freeing the array */
  ~MpqArray();
  /**
   * Obtain a constant pointer to the internal array.
   *
   * @return internal mpq_t array as a constant pointer
   */
  explicit operator const mpq_t *() const {
    return array;
  }

  /**
   * Obtain a pointer to the internal array.
   *
   * @return internal mpq_t array
   */
  explicit operator mpq_t *() {
    return array;
  }

 private:
  mpq_t *array; ///< array of mpq_t. It is allocated by AllocateMpqArray() and freed by FreeMpqArray().

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

} // namespace dlinear::qsopt_ex

#endif // DLINEAR5_DLINEAR_LIBS_QSOPT_EX_H_
