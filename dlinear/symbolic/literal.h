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

namespace dlinear {

using drake::symbolic::Variable;

using Literal = std::pair<Variable, bool>;
using LiteralSet = std::set<Literal>;
using Model = std::pair<std::vector<Literal>, std::vector<Literal>>;

std::ostream &operator<<(std::ostream &os, const Literal &literal);
std::ostream &operator<<(std::ostream &os, const LiteralSet &literals);
std::ostream &operator<<(std::ostream &os, const Model &model);

}  // namespace dlinear

// Needed for spdlog ranges.h. They share the same implementation of the operator<<.
std::ostream &operator<<(std::ostream &os, const ::dlinear::Literal &literal);
std::ostream &operator<<(std::ostream &os, const ::dlinear::Model &model);

namespace std {

template <>
bool operator==(const dlinear::Literal &x, const dlinear::Literal &y);
template <>
bool operator<=(const dlinear::Literal &x, const dlinear::Literal &y);

template <>
struct less<::dlinear::Literal> {
  bool operator()(const ::dlinear::Literal &a, const ::dlinear::Literal &b) const;
};

template <>
struct equal_to<::dlinear::Literal> {
  bool operator()(const ::dlinear::Literal &a, const ::dlinear::Literal &b) const;
};

template <>
struct less<::dlinear::LiteralSet> {
  bool operator()(const ::dlinear::LiteralSet &a, const ::dlinear::LiteralSet &b) const;
};

template <>
struct equal_to<::dlinear::LiteralSet> {
  bool operator()(const ::dlinear::LiteralSet &a, const ::dlinear::LiteralSet &b) const;
};

}  // namespace std
