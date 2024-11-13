/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "SmtResult.h"

#include <ostream>

#include "dlinear/util/error.h"

namespace dlinear {

std::ostream& operator<<(std::ostream& os, const SmtResult& bound) {
  switch (bound) {
    case SmtResult::UNSAT:
      return os << "unsat";
    case SmtResult::SKIP_SAT:
      return os << "skip-sat";
    case SmtResult::UNSOLVED:
      return os << "unsolved";
    case SmtResult::SAT:
      return os << "sat";
    case SmtResult::DELTA_SAT:
      return os << "delta-sat";
    case SmtResult::ERROR:
      return os << "error";
    case SmtResult::TIMEOUT:
      return os << "timeout";
    default:
      DLINEAR_UNREACHABLE();
  }
}

SmtResult operator~(const SmtResult result) {
  switch (result) {
    case SmtResult::SAT:
    case SmtResult::DELTA_SAT:
      return SmtResult::DELTA_SAT;
    default:
      return result;
  }
}

}  // namespace dlinear
