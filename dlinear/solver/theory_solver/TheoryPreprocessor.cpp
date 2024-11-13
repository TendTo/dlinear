/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "TheoryPreprocessor.h"

namespace dlinear {
TheoryPreprocessor::TheoryPreprocessor(const Config &config, const std::string &class_name)
    : config_{config}, stats_{config.with_timings(), class_name, "Total time spent in Process", "Total # of Process"} {}

}  // namespace dlinear
