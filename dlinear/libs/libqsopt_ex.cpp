/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */

#include "libqsopt_ex.h"

#include <iostream>

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

void MpqArray::AllocateMpqArray(size_t n_elements) {
  if (n_elements == 0) return;
  auto const memSize = static_cast<size_t>(sizeof(mpq_t) * n_elements + sizeof(size_t));

  size_t *newArray = nullptr;
  newArray = static_cast<std::size_t *>(calloc(1, memSize));
  if (!newArray) {
    fprintf(stderr, "EXIT: Not enough memory while allocating %zd bytes", memSize);
    exit(1);
  }

  newArray[0] = n_elements;
  array_ = reinterpret_cast<mpq_t *>(newArray + 1);
  for (size_t i = 0; i < n_elements; ++i) mpq_init(array_[i]);
}

void MpqArray::FreeMpqArray() {
  auto *sizeArray = reinterpret_cast<size_t *>(array_);
  if (sizeArray) sizeArray--;
  size_t nElements = sizeArray ? sizeArray[0] : 0;

  for (size_t i = 0; i < nElements; ++i) mpq_clear(array_[i]);
  free(sizeArray);
  array_ = nullptr;
}

MpqArray::MpqArray(size_t n_elements) : array_{nullptr} { AllocateMpqArray(n_elements); }

MpqArray::~MpqArray() { FreeMpqArray(); }

void MpqArray::Resize(size_t nElements) {
  {
    FreeMpqArray();
    AllocateMpqArray(nElements);
  }
}

std::ostream &operator<<(std::ostream &os, const MpqArray &array) {
  os << "[";
  for (int i = 0; i < static_cast<int>(array.size()); ++i) {
    os << array[i];
    if (i + 1u < array.size()) os << ", ";
  }
  os << "]";
  return os;
}

void QSXStart() { QSexactStart(); }

void QSXFinish() { QSexactClear(); }

}  // namespace dlinear::qsopt_ex
