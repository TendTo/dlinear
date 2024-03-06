/**
 * @file literal.cpp
 * @author dlinear
 * @date 15 Aug 2023
 * @copyright 2023 dlinear
 */

#include "literal.h"

namespace {
inline std::ostream &print_literal(std::ostream &os, const dlinear::Literal &literal) {
  return os << (literal.second ? "" : "¬") << literal.first;
}
inline std::ostream &print_model(std::ostream &os, const dlinear::Model &model) {
  os << "Boolean model:\n";
  for (const auto &lit : model.first) os << lit << " ";
  os << "\nTheory model:\n";
  for (const auto &lit : model.second) os << lit << " ";
  return os;
}
}  // namespace

namespace dlinear {

bool operator==(const Literal &a, const Literal &b) { return a.first.equal_to(b.first) && a.second == b.second; }

std::ostream &operator<<(std::ostream &os, const Literal &literal) { return print_literal(os, literal); }

std::ostream &operator<<(std::ostream &os, const Model &model) { return print_model(os, model); }
}  // namespace dlinear

std::ostream &operator<<(std::ostream &os, const dlinear::Literal &literal) { return print_literal(os, literal); }

std::ostream &operator<<(std::ostream &os, const dlinear::Model &model) { return print_model(os, model); }

bool std::less<dlinear::Literal>::operator()(const dlinear::Literal &a, const dlinear::Literal &b) const {
  return a.first.get_id() < b.first.get_id() || (a.first.equal_to(b.first) && a.second < b.second);
}
bool std::equal_to<dlinear::Literal>::operator()(const dlinear::Literal &a, const dlinear::Literal &b) const {
  return a.first.equal_to(b.first) && a.second == b.second;
}
