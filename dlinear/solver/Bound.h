#pragma once

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/LpColBound.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/logging.h"

namespace dlinear {

/** Bound. It is a tuple of value, bound type and index */
struct Bound {
  const mpq_class* value;  ///< Value of the bound
  LpColBound lp_bound;     ///< Type of the bound (e.g. L, SL, U, SU)
  LiteralSet explanation;  ///< Explanation for the existence of the bound

  std::strong_ordering operator<=>(const Bound& other) const;
  bool operator==(const Bound& other) const;
};

std::ostream& operator<<(std::ostream& os, const Bound& bound);

}  // namespace dlinear

OSTREAM_FORMATTER(dlinear::Bound)
