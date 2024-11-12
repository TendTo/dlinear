/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * LpBoundViolation struct.
 */
#pragma once

#include <iosfwd>

namespace dlinear {

struct LpBoundViolation {
  int column;
  bool upper_bound_violated;
};

std::ostream &operator<<(std::ostream &os, const LpBoundViolation &violation);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::LpBoundViolation);

#endif
