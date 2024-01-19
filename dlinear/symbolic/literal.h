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

#include <ostream>
#include <set>
#include <unordered_map>
#include <utility>
#include <vector>

#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

using Literal = std::pair<Variable, bool>;

struct LiteralComparator {
  bool operator()(const Literal &a, const Literal &b) const;
};

using LiteralSet = std::set<Literal, LiteralComparator>;

using Model = std::pair<std::vector<Literal>, std::vector<Literal>>;

std::ostream &operator<<(std::ostream &os, const Literal &literal);
std::ostream &operator<<(std::ostream &os, const LiteralSet &literal_set);
std::ostream &operator<<(std::ostream &os, const std::vector<Literal> &literal_vec);
std::ostream &operator<<(std::ostream &os, const Model &model);

}  // namespace dlinear
