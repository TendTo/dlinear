/**
 * @file literal.h
 * @author dlinear
 * @date 15 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */

#ifndef DLINEAR5_DLINEAR_SYMBOLIC_LITERAL_H_
#define DLINEAR5_DLINEAR_SYMBOLIC_LITERAL_H_

#include <set>
#include "dlinear/symbolic/symbolic.h"

namespace dlinear {

using Literal = std::pair<Variable, bool>;

struct LiteralComparator {
  bool operator()(const Literal &a, const Literal &b) const;
};

using LiteralSet = std::set<Literal, LiteralComparator>;

} // namespace dlinear

#endif //DLINEAR5_DLINEAR_SYMBOLIC_LITERAL_H_
