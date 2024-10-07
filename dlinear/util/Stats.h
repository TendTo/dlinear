/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Stats class.
 */
#pragma once

#include <atomic>
#include <iosfwd>
#include <string>

#include "dlinear/util/Timer.h"

namespace dlinear {

/**
 * Dataclass collecting statistics about some operation or process.
 *
 * At its more basic level, it collects the cumulative time spent in a given operation.
 */
class Stats {
 private:
  Timer timer_;  ///< Timer object to measure the cumulative time spent in the operation

 protected:
  bool enabled_;            ///< Flag to enable/disable the collection of statistics
  std::string class_name_;  ///< Name of the class running the operation the Stats object is collecting statistics for
  std::string operations_name_;  ///< Name of the operation the Stats object is collecting statistics for

 public:
  /**
   * Construct a Stats object.
   * @param enabled whether the Stats object should be enabled or not. Its value is propagated to the @ref timer_
   * @param class_name name of the class running the operation the Stats object is collecting statistics for
   * @param name_time name of the operation the Stats object is collecting statistics for
   */
  explicit Stats(bool enabled, std::string class_name, std::string name_time = "Time spent in Operations");
  Stats(const Stats &other) = default;
  Stats &operator=(const Stats &other) = default;
  virtual ~Stats() = default;

  Stats &operator+=(const Stats &other);
  Stats operator+(const Stats &other) const;

  /** @checker{enabled, stats} */
  [[nodiscard]] bool enabled() const { return enabled_; }
  /** @getsetter{timer, stats} */
  [[nodiscard]] Timer &m_timer() { return timer_; }
  /** @getter{timer, stats} */
  [[nodiscard]] const Timer &timer() const { return timer_; }
  /**
   * Convert the current state of the object to a formatted string, only including the specific
   * part the Stat object is concerned about
   * @return string representing a partial state of the Stats
   */
  [[nodiscard]] virtual std::string ToSegmentString() const;
  /**
   * Convert the current state of the object to a formatted string
   * @return string representing the state of the Stats
   */
  [[nodiscard]] virtual std::string ToString() const;
};

/**
 * Dataclass collecting statistics about some operation or process.
 *
 * Not only does it collect the cumulative time spent in a given operation, but also the total number of iterations.
 */
class IterationStats : public Stats {
 private:
  std::atomic<unsigned int> iterations_;  ///< Atomic counter for the total number of iterations
  std::string iterations_name_;           ///< Name to give to the iteration operation

 public:
  /**
   * Construct an IterationStats object.
   * @param enabled whether the Stats object should be enabled or not. Its value is propagated to the @ref timer_
   * @param class_name name of the class running the operation the Stats object is collecting statistics for
   * @param name_time name of the operation the Stats object is collecting statistics for
   * @param iterations_name name of the operation the Stats object is collecting statistics for
   */
  explicit IterationStats(bool enabled, std::string class_name, std::string name_time = "Time spent in Operations",
                          std::string iterations_name = "Total # of Iterations");
  IterationStats(const IterationStats &other);
  IterationStats &operator=(const IterationStats &other);

  IterationStats &operator+=(const IterationStats &other);
  IterationStats operator+(const IterationStats &other) const;

  [[nodiscard]] std::string ToSegmentString() const override;

  [[nodiscard]] std::string ToString() const override;

  /**
   * Increase the iteration counter by one.
   * @note The iteration counter is atomic.
   */
  void Increase();

  /** @getter{iterations, stats} */
  [[nodiscard]] unsigned int iterations() const { return iterations_.load(); }

  void operator++();
  void operator++(int);
};

std::ostream &operator<<(std::ostream &os, const Stats &stats);
std::ostream &operator<<(std::ostream &os, const IterationStats &stats);

}  // namespace dlinear
