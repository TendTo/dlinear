/**
 * @file sort.cpp
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 */
#include "sort.h"

using std::ostream;
using std::string;

namespace dlinear {

Sort ParseSort(const string &s) {
  if (s == "Real") {
    return Sort::Real;
  }
  if (s == "Int") {
    return Sort::Int;
  }
  if (s == "Bool") {
    return Sort::Bool;
  }
  if (s == "Binary") {
    return Sort::Binary;
  }
  DLINEAR_RUNTIME_ERROR_FMT("{} is not one of {Real, Int, Bool}.", s);
}

ostream &operator<<(ostream &os, const Sort &sort) {
  switch (sort) {
    case Sort::Bool:return os << "Bool";
    case Sort::Int:return os << "Int";
    case Sort::Real:return os << "Real";
    case Sort::Binary:return os << "Binary";
    default:DLINEAR_UNREACHABLE();
  }
}

Variable::Type SortToType(Sort sort) {
  switch (sort) {
    case Sort::Binary:return Variable::Type::BINARY;
    case Sort::Bool:return Variable::Type::BOOLEAN;
    case Sort::Int:return Variable::Type::INTEGER;
    case Sort::Real:return Variable::Type::CONTINUOUS;
  }
  DLINEAR_UNREACHABLE();
}

}  // namespace dlinear
