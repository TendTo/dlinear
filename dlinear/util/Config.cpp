/**
 * @file Config.cpp
 * @author tend
 * @date 07 Aug 2023
 * @copyright 2023 tend
 */
#include "dlinear/util/Config.h"

namespace dlinear {
ostream &operator<<(ostream &os, const Config &config) {
  os << "Config {" << endl
     << "\t_verbosity=" << config.verbosity_ << endl
     << "\t_precision=" << config.precision_ << endl
     << "\t_produceModels=" << config.produceModels_ << endl
     << "\t_randomSeed=" << config.randomSeed_ << endl
     << '}';
  return os;
}
} // namespace dlinear
