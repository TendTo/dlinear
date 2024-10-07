/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */

#include "libqsopt_ex.h"

namespace dlinear::qsopt_ex {

mpq_class *StringToMpqPtr(const std::string &str) { return CStringToMpqPtr(str.c_str()); }
mpq_class StringToMpq(const std::string &str) { return CStringToMpq(str.c_str()); }
mpq_class *CStringToMpqPtr(const char str[]) {
  mpq_t val;
  mpq_init(val);
  mpq_EGlpNumReadStr(val, str);
  auto result = new mpq_class(val);
  mpq_clear(val);
  return result;
}
mpq_class CStringToMpq(const char str[]) {
  mpq_t val;
  mpq_init(val);
  mpq_EGlpNumReadStr(val, str);
  mpq_class result(val);
  mpq_clear(val);
  return result;
}

void MpqArray::AllocateMpqArray(size_t nElements) {
  auto const memSize = static_cast<size_t>(sizeof(mpq_t) * nElements + sizeof(size_t));
  void *newArray = nullptr;
  if (memSize) {
    newArray = calloc(1, memSize);
    if (!newArray) {
      fprintf(stderr, "EXIT: Not enough memory while allocating %zd bytes", memSize);
      exit(1);
    }
  }
  size_t *sizeArray = nElements ? static_cast<size_t *>(newArray) : nullptr;
  if (nElements) sizeArray[0] = nElements;

  array = reinterpret_cast<mpq_t *>(nElements ? (sizeArray + 1) : nullptr);
  for (size_t i = 0; i < nElements; ++i) mpq_init(array[i]);
}

void MpqArray::FreeMpqArray() {
  auto *sizeArray = reinterpret_cast<size_t *>(array);
  if (sizeArray) sizeArray--;
  size_t nElements = sizeArray ? sizeArray[0] : 0;

  for (size_t i = 0; i < nElements; ++i) mpq_clear(array[i]);
  free(sizeArray);
  array = nullptr;
}

MpqArray::MpqArray(size_t nElements) : array{nullptr} { AllocateMpqArray(nElements); }

MpqArray::~MpqArray() { FreeMpqArray(); }

void MpqArray::Resize(size_t nElements) {
  {
    FreeMpqArray();
    AllocateMpqArray(nElements);
  }
}

void QSXStart() { QSexactStart(); }

void QSXFinish() { QSexactClear(); }

}  // namespace dlinear::qsopt_ex
