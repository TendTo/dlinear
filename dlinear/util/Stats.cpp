/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "Stats.h"

#include <fmt/core.h>

#include <chrono>
#include <ostream>
#include <utility>

#define DLINEAR_STATS_FMT "{:<35} @ {:<26} = {:>15} sec"
#define DLINEAR_ITERATION_STATS_FMT "{:<35} @ {:<26} = {:>15}"

namespace dlinear {

Stats::Stats(const bool enabled, std::string class_name, std::string operations_name)
    : timer_{}, enabled_{enabled}, class_name_{std::move(class_name)}, operations_name_{std::move(operations_name)} {}

std::string Stats::ToSegmentString() const {
  return fmt::format(DLINEAR_STATS_FMT, operations_name_, class_name_, timer_.seconds());
}
std::string Stats::ToString() const { return Stats::ToSegmentString(); }

Stats &Stats::operator+=(const Stats &other) {
  if (class_name_.empty() && !other.class_name_.empty()) class_name_ = other.class_name_;
  if (operations_name_.empty() && !other.operations_name_.empty()) operations_name_ = other.operations_name_;
  timer_ += other.timer_;
  return *this;
}
Stats Stats::operator+(const Stats &other) const {
  Stats result{*this};
  result += other;
  return result;
}

void IterationStats::Increase() {
  if (enabled_) std::atomic_fetch_add_explicit(&iterations_, 1, std::memory_order_relaxed);
}

std::string IterationStats::ToSegmentString() const {
  return fmt::format(DLINEAR_ITERATION_STATS_FMT, iterations_name_, class_name_, iterations_.load());
}
std::string IterationStats::ToString() const { return IterationStats::ToSegmentString() + "\n" + Stats::ToString(); }

IterationStats::IterationStats(bool enabled, std::string class_name, std::string operations_name,
                               std::string iterations_name)
    : Stats(enabled, std::move(class_name), std::move(operations_name)),
      iterations_{0},
      iterations_name_{std::move(iterations_name)} {}
IterationStats::IterationStats(const dlinear::IterationStats &other)
    : Stats(other), iterations_{other.iterations_.load()}, iterations_name_{other.iterations_name_} {}

void IterationStats::operator++() { Increase(); }
void IterationStats::operator++(int) { Increase(); }
IterationStats &IterationStats::operator=(const IterationStats &other) {
  if (this != &other) {
    Stats::operator=(other);
    iterations_ = other.iterations_.load();
    iterations_name_ = other.iterations_name_;
  }
  return *this;
}
IterationStats &IterationStats::operator+=(const IterationStats &other) {
  Stats::operator+=(other);
  if (iterations_name_.empty() && !other.iterations_name_.empty()) iterations_name_ = other.iterations_name_;
  std::atomic_fetch_add_explicit(&iterations_, other.iterations_.load(), std::memory_order_relaxed);
  return *this;
}
IterationStats IterationStats::operator+(const IterationStats &other) const {
  IterationStats result{*this};
  result += other;
  return result;
}

std::ostream &operator<<(std::ostream &os, const Stats &stats) { return os << stats.ToString(); }
std::ostream &operator<<(std::ostream &os, const IterationStats &stats) { return os << stats.ToString(); }

}  // namespace dlinear
