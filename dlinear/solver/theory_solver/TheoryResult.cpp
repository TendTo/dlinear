/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "TheoryResult.h"

#include <ostream>

#include "dlinear/util/error.h"

namespace dlinear {

std::ostream &operator<<(std::ostream &os, const TheoryResult result) {
  switch (result) {
    case TheoryResult::UNSOLVED:
      return os << "unsolved";
    case TheoryResult::SAT:
      return os << "sat";
    case TheoryResult::DELTA_SAT:
      return os << "delta-sat";
    case TheoryResult::UNSAT:
      return os << "unsat";
    case TheoryResult::ERROR:
      return os << "error";
    default:
      DLINEAR_UNREACHABLE();
  }
}

TheoryResult operator~(const TheoryResult result) {
  switch (result) {
    case TheoryResult::SAT:
    case TheoryResult::DELTA_SAT:
      return TheoryResult::DELTA_SAT;
    default:
      return result;
  }
}

}  // namespace dlinear
