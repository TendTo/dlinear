/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "TheoryPropagator.h"

namespace dlinear {
TheoryPropagator::TheoryPropagator(const Config &config, const std::string &class_name)
    : config_{config},
      stats_{config.with_timings(), class_name, "Total time spent in Propagate", "Total # of Propagate"} {}
}  // namespace dlinear
