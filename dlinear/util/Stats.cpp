/**
 * @file Stats.cpp
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 */
#include "Stats.h"

using std::endl;
using std::ostream;

namespace dlinear {

ostream &operator<<(ostream &os, const Stats &stats) { return os << stats.ToString(); }

}  // namespace dlinear
