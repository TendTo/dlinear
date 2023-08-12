/**
 * @file qsoptex.h
 * @author tend
 * @date 10 Aug 2023
 * @copyright 2023 tend
 * @brief Qsopt_ex wrapper.
 *
 * This header includes the Qsopt_ex library and provides a various helpers.
 * Other files in the library should depend on this header instead of the Qsopt_ex library directly.
 * Instead of including <qsopt_ex/Qsopt_ex.h>, include "dlinear/libs/qsoptex.h".
 * In the build files, instead of depending on "@qsoptex", depend on "//dlinear/libs:qsoptex".
 */

#ifndef DLINEAR5_DLINEAR_LIBS_QSOPTEX_H_
#define DLINEAR5_DLINEAR_LIBS_QSOPTEX_H_

#include <gmpxx.h>

extern "C"
{
#include <qsopt_ex/QSopt_ex.h>
}

// These #defines from <qsopt_ex/QSopt_ex.h> cause problems for us
#undef OPTIMAL
#undef DUAL_INFEASIBLE

using std::string;

namespace dlinear::qsoptex {

mpq_class *StringToMpqPtr(const std::string &str);
mpq_class StringToMpq(const std::string &str);

/**
 * @brief A wrapper around an array of mpq_t elements.
 *
 * It is used to pass around arrays of mpq_t, ensuring they are cleaned up after use.
 * The array is allocated by AllocateMpqArray() and freed by FreeMpqArray().
 */
class MpqArray {
 public:
  /**
   * @brief Construct a new MpqArray object, allocating the array with @p nElements elements.
   *
   * @param nElements The number of elements in the array.
   */
  explicit MpqArray(size_t nElements);
  /**
   * @brief Destroy the MpqArray object, freeing the array.
   */
  ~MpqArray();
  /**
   * @brief Obtain a constant pointer to the internal array.
   *
   * @return internal mpq_t array as a constant pointer
   */
  explicit operator const mpq_t *() const {
    return array;
  }

  /**
   * @brief Obtain a pointer to the internal array.
   *
   * @return internal mpq_t array
   */
  explicit operator mpq_t *() {
    return array;
  }

 private:
  mpq_t *array; ///< array of mpq_t. It is allocated by AllocateMpqArray() and freed by FreeMpqArray().

  /**
   * @brief Allocate the array with @p nElements elements.
   *
   * The array has a peculiar structure, where the element at index -1 is the size of the array.
   * @param nElements The number of elements in the array.
   */
  void AllocateMpqArray(size_t nElements);

  /**
   * @brief Free the array of mpq_t.
   */
  void FreeMpqArray();
};

void QSXStart();
void QSXFinish();

} // namespace dlinear::qsoptex

#endif // DLINEAR5_DLINEAR_LIBS_QSOPTEX_H_
