/**
 * @file Logic.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "Logic.h"

#include "dlinear/util/exception.h"

using std::ostream;
using std::string;

namespace dlinear {

Logic parseLogic(const string &s) {
  if (s == "QF_NRA") return Logic::QF_NRA;
  if (s == "QF_NRA_ODE") return Logic::QF_NRA_ODE;
  if (s == "QF_LRA") return Logic::QF_LRA;
  if (s == "QF_RDL") return Logic::QF_RDL;
  if (s == "QF_LIA") return Logic::QF_LIA;
  DLINEAR_RUNTIME_ERROR_FMT("set-logic '{}' is not supported", s);
}

ostream &operator<<(ostream &os, const Logic &logic) {
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
    default:
      DLINEAR_UNREACHABLE();
  }
}

}  // namespace dlinear
