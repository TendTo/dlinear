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

#include <functional>
#include <ostream>
#include <set>
#include <unordered_map>
#include <utility>
#include <vector>

#include "dlinear/symbolic/symbolic_variable.h"
#include "dlinear/util/logging.h"

namespace dlinear {

using drake::symbolic::Variable;

struct Literal {
  Variable var;
  bool truth;
};
using LiteralSet = std::set<Literal>;
using Model = std::pair<std::vector<Literal>, std::vector<Literal>>;

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
