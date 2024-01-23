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
#include <string>

#include "dlinear/util/Timer.h"

namespace dlinear {

class Stats {
 private:
  Timer timer_;

 protected:
  const bool enabled_;
  std::string class_name_;
  std::string operations_name_;

 public:
  explicit Stats(bool enabled, std::string class_name, std::string name_time = "Time spent in Operations");

  virtual ~Stats();

  /**
   * Return whether the stats is enabled.
   * @return whether the stats is enabled.
   */
  [[nodiscard]] bool enabled() const { return enabled_; }
  /**
   * Return a mutable reference to the timer
   * @return timer
   */
  [[nodiscard]] Timer &m_timer() { return timer_; }
  /**
   * Return a constant reference to the timer
   * @return timer
   */
  [[nodiscard]] const Timer &timer() const { return timer_; }
  /**
   * @brief Convert the current state of the object to a formatted string, only including the specific
   * part the Stat object is concerned about
   * @return string representing a partial state of the Stats
   */
  [[nodiscard]] virtual std::string ToSegmentString() const;
  /**
   * @brief Convert the current state of the object to a formatted string
   * @return string representing the state of the Stats
   */
  [[nodiscard]] virtual std::string ToString() const;
};

class IterationStats : public Stats {
 private:
  std::atomic<unsigned int> iterations_;
  std::string iterations_name_;

 public:
  explicit IterationStats(bool enabled, std::string class_name, std::string name_time = "Time spent in Operations",
                          std::string iterations_name = "Total # of Iterations");

  ~IterationStats() override;

  [[nodiscard]] std::string ToSegmentString() const override;

  [[nodiscard]] std::string ToString() const override;

  /**
   * Increase the iteration counter by one.
   * @note The iteration counter is atomic.
   */
  void Increase();

  void operator++();
  void operator++(int);
};

std::ostream &operator<<(std::ostream &os, const Stats &stats);
std::ostream &operator<<(std::ostream &os, const IterationStats &stats);

}  // namespace dlinear
