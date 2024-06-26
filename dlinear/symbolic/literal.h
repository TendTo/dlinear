/**
 * @file literal.h
 * @author dlinear
 * @date 15 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */
#pragma once

#include <compare>
#include <ostream>
#include <set>
#include <utility>
#include <vector>

#include "dlinear/symbolic/symbolic_variable.h"  // IWYU pragma: export
#include "dlinear/util/logging.h"

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

bool operator==(const dlinear::LiteralSet &lhs, const dlinear::LiteralSet &rhs);
std::strong_ordering operator<=>(const dlinear::LiteralSet &lhs, const dlinear::LiteralSet &rhs);

std::ostream &operator<<(std::ostream &os, const std::vector<Variable> &variables);
std::ostream &operator<<(std::ostream &os, const Literal &literal);
std::ostream &operator<<(std::ostream &os, const LiteralSet &literals);
std::ostream &operator<<(std::ostream &os, const Model &model);
std::ostream &operator<<(std::ostream &os, const std::vector<Literal> &variables);

}  // namespace dlinear

OSTREAM_FORMATTER(dlinear::Variable)
OSTREAM_FORMATTER(dlinear::Variable::Type)
OSTREAM_FORMATTER(dlinear::Literal)
OSTREAM_FORMATTER(dlinear::LiteralSet)
OSTREAM_FORMATTER(dlinear::Model)
