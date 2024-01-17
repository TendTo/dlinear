/**
 * @file Stats.cpp
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 */
#include "Stats.h"

#include <spdlog/fmt/fmt.h>

using std::endl;
using std::ostream;

namespace dlinear {

Stats::Stats(const bool enabled, std::string class_name, std::string operations_name)
    : timer_{}, enabled_{enabled}, class_name_{std::move(class_name)}, operations_name_{std::move(operations_name)} {}

Stats::~Stats() {
  if (enabled_) std::cout << Stats::ToString() << std::endl;
}

std::string Stats::ToString() const {
  return fmt::format(DLINEAR_STATS_FMT, operations_name_, class_name_, timer_.seconds());
}

void IterationStats::Increase() {
  if (enabled_) atomic_fetch_add_explicit(&iterations_, 1, std::memory_order_relaxed);
}

std::string IterationStats::ToString() const {
  return fmt::format(DLINEAR_ITERATION_STATS_FMT, iterations_name_, class_name_, iterations_.load()) +
         Stats::ToString();
}

ostream &operator<<(ostream &os, const Stats &stats) { return os << stats.ToString(); }

IterationStats::IterationStats(bool enabled, std::string class_name, std::string operations_name,
                               std::string iterations_name)
    : Stats(enabled, std::move(class_name), std::move(operations_name)),
      iterations_{0},
      iterations_name_{std::move(iterations_name)} {}

IterationStats::~IterationStats() {
  if (enabled_) std::cout << IterationStats::ToString() << std::endl;
}

void IterationStats::operator++() { Increase(); }
void IterationStats::operator++(int) { Increase(); }

std::ostream &operator<<(ostream &os, const IterationStats &stats) { return os << stats.ToString(); }

}  // namespace dlinear
