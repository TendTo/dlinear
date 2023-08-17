/**
 * @file Stats.cpp
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 */
#include "Stats.h"

namespace dlinear {

ostream &operator<<(ostream &os, const Stats &stats) {
  os << "Stats {" << endl
     << "\t_enabled=" << stats.enabled_ << endl
     << '}';
  return os;
}

} // namespace dlinear
