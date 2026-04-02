/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Row struct.
 */
#pragma once

#include <iosfwd>
#include <optional>
#include <utility>
#include <vector>

#include "dlinear/libs/libgmp.h"
#include "dlinear/parser/mps/Sense.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear::mps {

/**
 * Structure representing a row in the LP solver in the form of a linear combination of variables.
 * Missing bounds are represented by `std::nullopt`, which means that the row is unbounded in that direction.
 * E.g. `lb` = `std::nullopt` and `ub` = `5` represents a row such that @f$ -\infty \leq \text{addends} \leq 5 @f$.
 */
struct Row {
  Row() = default;
  explicit Row(const Sense _sense) : addends{}, lb{}, ub{}, sense{_sense} {}
  std::map<Expression, mpq_class> addends;  ///< Linear combination of variables
  std::optional<mpq_class> lb;              ///< Lower bound. If`std::nullopt`, indicated unboundness
  std::optional<mpq_class> ub;              ///< Upper bound. If`std::nullopt`, indicated unboundness
  Sense sense{Sense::N};                    ///< SenseType of the row
};

std::ostream& operator<<(std::ostream& os, const Row& row);

}  // namespace dlinear::mps

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::mps::Row)

#endif
