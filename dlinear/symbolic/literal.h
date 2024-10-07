/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Collection of data structures and functions for working with literals.
 *
 * Literals are a pair formed by a boolean variable and a truth value indicating whether the variable is negated or not.
 */
#pragma once

#include <compare>
#include <ostream>
#include <set>
#include <utility>
#include <vector>

#include "dlinear/symbolic/symbolic_variable.h"  // IWYU pragma: export

namespace dlinear {

using drake::symbolic::Variable;

/** A literal is a variable with an associated truth value, indicating whether it is true or false. */
struct Literal {
  Variable var;  ///< Variable.
  bool truth;    ///< Truth value.
};
using LiteralSet = std::set<Literal>;                                 ///< A set of literals.
using Model = std::pair<std::vector<Literal>, std::vector<Literal>>;  ///< A model is a pair of two vectors of literals.

bool operator==(const dlinear::Literal &lhs, const dlinear::Literal &rhs);
std::strong_ordering operator<=>(const dlinear::Literal &lhs, const dlinear::Literal &rhs);
inline Literal operator!(const Literal &l) { return {l.var, !l.truth}; }

bool operator==(const dlinear::LiteralSet &lhs, const dlinear::LiteralSet &rhs);
std::strong_ordering operator<=>(const dlinear::LiteralSet &lhs, const dlinear::LiteralSet &rhs);

std::ostream &operator<<(std::ostream &os, const std::vector<Variable> &variables);
std::ostream &operator<<(std::ostream &os, const Literal &literal);
std::ostream &operator<<(std::ostream &os, const LiteralSet &literals);
std::ostream &operator<<(std::ostream &os, const Model &model);
std::ostream &operator<<(std::ostream &os, const std::vector<Literal> &variables);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::Variable)
OSTREAM_FORMATTER(dlinear::Variable::Type)
OSTREAM_FORMATTER(dlinear::Literal)
OSTREAM_FORMATTER(dlinear::LiteralSet)
OSTREAM_FORMATTER(dlinear::Model)

#endif
