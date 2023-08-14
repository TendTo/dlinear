/**
 * @file Stats.cpp
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 */
#include "Stats.h"

namespace dlinear {
template<typename T>
void Stats::increase(atomic<T> *v) {
  if (enabled_) {
    DLINEAR_TRACE("Stats::increase");
    atomic_fetch_add_explicit(v, 1, memory_order_relaxed);
  }
}

ostream &operator<<(ostream &os, const Stats &stats) {
  os << "Stats {" << endl
     << "\t_enabled=" << stats.enabled_ << endl
     << '}';
  return os;
}
} // namespace dlinear
