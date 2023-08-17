/**
 * @file literal.cpp
 * @author dlinear
 * @date 15 Aug 2023
 * @copyright 2023 dlinear
 */

#include "literal.h"

namespace dlinear {

bool LiteralComparator::operator()(const Literal &a, const Literal &b) const {
  if (a.first.get_id() < b.first.get_id()) {
    return true;
  } else if (a.first.get_id() > b.first.get_id()) {
    return false;
  }
  return a.second < b.second;
}

} // namespace dlinear