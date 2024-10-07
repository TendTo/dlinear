/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "Logic.h"

#include "dlinear/util/exception.h"

namespace dlinear {

Logic parseLogic(const std::string &s) {
  if (s == "QF_NRA") return Logic::QF_NRA;
  if (s == "QF_NRA_ODE") return Logic::QF_NRA_ODE;
  if (s == "QF_LRA") return Logic::QF_LRA;
  if (s == "QF_RDL") return Logic::QF_RDL;
  if (s == "QF_LIA") return Logic::QF_LIA;
  if (s == "LRA") return Logic::LRA;
  DLINEAR_RUNTIME_ERROR_FMT("set-logic '{}' is not supported", s);
}

std::ostream &operator<<(std::ostream &os, const Logic &logic) {
  switch (logic) {
    case Logic::QF_NRA:
      return os << "QF_NRA";
    case Logic::QF_NRA_ODE:
      return os << "QF_NRA_ODE";
    case Logic::QF_LRA:
      return os << "QF_LRA";
    case Logic::QF_RDL:
      return os << "QF_RDL";
    case Logic::QF_LIA:
      return os << "QF_LIA";
    case Logic::LRA:
      return os << "LRA";
    default:
      DLINEAR_UNREACHABLE();
  }
}

}  // namespace dlinear
