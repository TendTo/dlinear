/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "Sort.h"

#include "dlinear/util/exception.h"

namespace dlinear::vnnlib {

Sort ParseSort(const std::string &s) {
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
  DLINEAR_RUNTIME_ERROR_FMT("{} is not one of [Real, Int, Bool, Binary].", s);
}

std::ostream &operator<<(std::ostream &os, const Sort &sort) {
  switch (sort) {
    case Sort::Bool:
      return os << "Bool";
    case Sort::Int:
      return os << "Int";
    case Sort::Real:
      return os << "Real";
    case Sort::Binary:
      return os << "Binary";
    default:
      DLINEAR_UNREACHABLE();
  }
}

Variable::Type SortToType(Sort sort) {
  switch (sort) {
    case Sort::Binary:
      return Variable::Type::BINARY;
    case Sort::Bool:
      return Variable::Type::BOOLEAN;
    case Sort::Int:
      return Variable::Type::INTEGER;
    case Sort::Real:
      return Variable::Type::CONTINUOUS;
  }
  DLINEAR_UNREACHABLE();
}

}  // namespace dlinear::vnnlib
