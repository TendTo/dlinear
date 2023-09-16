/**
 * @file Stats.h
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 * Stats class.
 * Used as a base class for more specialized stats classes.
 *
 * Simple dataclass to store the statistics of a solver run.
 */
#pragma once

#include <atomic>
#include <iostream>

namespace dlinear {

class Stats {
 private:
  const bool enabled_{false};

 protected:
  template <typename T>
  void increase(std::atomic<T> *v) {
    if (enabled_) {
      atomic_fetch_add_explicit(v, 1, std::memory_order_relaxed);
    }
  }

 public:
  explicit Stats(bool enabled) : enabled_{enabled} {}

  Stats(const Stats &) = default;

  Stats(Stats &&) = default;

  Stats &operator=(const Stats &) = delete;

  Stats &operator=(Stats &&) = delete;

  virtual ~Stats() = default;

  /**
   * Return whether the stats is enabled.
   * @return whether the stats is enabled.
   */
  [[nodiscard]] bool enabled() const { return enabled_; }

  friend std::ostream &operator<<(std::ostream &os, const Stats &stats);
};

}  // namespace dlinear
