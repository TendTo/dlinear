/**
 * @file Stats.cpp
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 */
#include "Stats.h"

#include <spdlog/fmt/fmt.h>

#include <utility>

#define DLINEAR_STATS_FMT "{:<35} @ {:<26} = {:>15} sec"
#define DLINEAR_ITERATION_STATS_FMT "{:<35} @ {:<26} = {:>15}"

namespace dlinear {

Stats::Stats(const bool enabled, std::string class_name, std::string operations_name)
    : timer_{}, enabled_{enabled}, class_name_{std::move(class_name)}, operations_name_{std::move(operations_name)} {}

Stats::~Stats() {
  if (enabled_) std::cout << Stats::ToSegmentString() << std::endl;
}

std::string Stats::ToSegmentString() const {
  return fmt::format(DLINEAR_STATS_FMT, operations_name_, class_name_, timer_.seconds());
}
std::string Stats::ToString() const { return Stats::ToSegmentString(); }

void IterationStats::Increase() {
  if (enabled_) atomic_fetch_add_explicit(&iterations_, 1, std::memory_order_relaxed);
}

std::string IterationStats::ToSegmentString() const {
  return fmt::format(DLINEAR_ITERATION_STATS_FMT, iterations_name_, class_name_, iterations_.load());
}
std::string IterationStats::ToString() const { return IterationStats::ToSegmentString() + Stats::ToString(); }

IterationStats::IterationStats(bool enabled, std::string class_name, std::string operations_name,
                               std::string iterations_name)
    : Stats(enabled, std::move(class_name), std::move(operations_name)),
      iterations_{0},
      iterations_name_{std::move(iterations_name)} {}

IterationStats::~IterationStats() {
  if (enabled_) std::cout << IterationStats::ToSegmentString() << std::endl;
}

void IterationStats::operator++() { Increase(); }
void IterationStats::operator++(int) { Increase(); }

std::ostream &operator<<(std::ostream &os, const Stats &stats) { return os << stats.ToString(); }
std::ostream &operator<<(std::ostream &os, const IterationStats &stats) { return os << stats.ToString(); }

}  // namespace dlinear
