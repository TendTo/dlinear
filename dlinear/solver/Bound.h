/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Bound class.
 */
#pragma once

#include <utility>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/LpColBound.h"
#include "dlinear/symbolic/literal.h"

namespace dlinear {

/** Bound. It is a tuple of value, bound type and index */
struct Bound {
  Bound() = default;
  Bound(const mpq_class* value_, LpColBound lp_bound_, Literal theory_literal_, LiteralSet explanation_)
      : value{value_},
        lp_bound{lp_bound_},
        theory_literal{std::move(theory_literal_)},
        explanation{std::move(explanation_)} {}
  Bound(const mpq_class* value_, LpColBound lp_bound_, Literal theory_literal_)
      : value{value_}, lp_bound{lp_bound_}, theory_literal{std::move(theory_literal_)}, explanation{} {}

  const mpq_class* value;  ///< Value of the bound
  LpColBound lp_bound;     ///< Type of the bound (e.g. L, SL, U, SU)
  Literal theory_literal;  ///< Theory literal associated with the bound
  LiteralSet explanation;  ///< Explanation for the existence of the bound (e.g. propagation)

  std::strong_ordering operator<=>(const Bound& other) const;
  bool operator==(const Bound& other) const;
};

std::ostream& operator<<(std::ostream& os, const Bound& bound);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::Bound)

#endif
