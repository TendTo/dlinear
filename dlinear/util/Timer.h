/**
 * @file Timer.h
 * @author dlinear
 * @date 16 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */

#ifndef DLINEAR5_DLINEAR_UTIL_TIMER_H_
#define DLINEAR5_DLINEAR_UTIL_TIMER_H_

#include <sys/resource.h>

#include <chrono>
#include <iostream>
#include <type_traits>
#include <cstdint>

namespace dlinear {

/**
 * Timer class.
 *
 * Simple timer class to evaluate the performance of the software.
 */
template<typename T>
class TimerBase {
 public:
  using clock = T;
  typedef typename clock::duration duration;
  typedef typename clock::time_point time_point;

  TimerBase();

  /**
   * Start the timer.
   *
   * The timer is reset to zero.
   */
  void start();

  /**
   * Pause the timer.
   *
   * If the timer is not running, this function does nothing.
   */
  void pause();

  /**
   * Resume the timer.
   *
   * If the timer is not running, this function does nothing.
   */
  void resume();

  /**
   * Check if the timer is running.
   * @return whether the timer is running
   */
  [[nodiscard]] bool is_running() const;

  /**
   * Return the elapsed time.
   * @return the elapsed time as duration
   */
  [[nodiscard]] duration elapsed() const;

  /**
   * Return the elapsed time.
   * @return the elapsed time in seconds
   */
  [[nodiscard]] std::chrono::duration<double>::rep seconds() const;

 protected:
  [[nodiscard]] time_point now() const { return clock::now(); }

 private:
  bool running_{false}; ///< Whether the timer is running or not.
  time_point last_start_{}; ///< Last time_point when the timer is started or resumed.
  duration elapsed_{}; ///< Elapsed time so far. This doesn't include the current fragment if it is running.
};

// Use high_resolution clock if it's steady, otherwise use steady_clock.
using chosen_steady_clock = std::conditional<std::chrono::high_resolution_clock::is_steady,
                                             std::chrono::high_resolution_clock,
                                             std::chrono::steady_clock>::type;

extern template
class TimerBase<chosen_steady_clock>;
class Timer : public TimerBase<chosen_steady_clock> {};

struct user_clock {  // Implements the Clock interface of std::chrono
  typedef uint64_t rep;
  typedef std::micro period;
  typedef std::chrono::duration<rep, period> duration;
  typedef std::chrono::time_point<user_clock> time_point;
  const bool is_steady = false;  // Not sure how this should be interpreted here
  static time_point now();
};

extern template
class TimerBase<user_clock>;
class UserTimer : public TimerBase<user_clock> {};

/**
 * TimerGuard class.
 *
 * Wraps a timer object and pauses it when the guard object is destructed.
 */
class TimerGuard {
 public:
  /**
   * TimerGuard constructor.
   *
   * If @p enabled is false, this class does not do anything.
   * If @p start_timer is true, starts the @p timer in the constructor.
   * Otherwise, it does not start it and a user has to call `resume()` to start it.
   * @param timer the timer to be guarded
   * @param enabled whether the timer is enabled
   * @param start_timer whether the timer should be started
   */
  TimerGuard(Timer *timer, bool enabled, bool start_timer = true);

  TimerGuard(const TimerGuard &) = delete;
  TimerGuard(TimerGuard &&) = delete;
  TimerGuard &operator=(const TimerGuard &) = delete;
  TimerGuard &operator=(TimerGuard &&) = delete;

  /**
   * When the timer guard object is destructed, it pauses the embedded timer object.
   * If the timer is not enabled, this function does nothing.
   */
  ~TimerGuard();

  /** Pause the guarded timer object */
  void pause();

  /** Resume the guarded timer object */
  void resume();

 private:
  Timer *const timer_; ///< The timer to be guarded.
  const bool enabled_{false}; ///< Whether the timer is enabled.
};

extern UserTimer main_timer;

}  // namespace dlinear

#endif //DLINEAR5_DLINEAR_UTIL_TIMER_H_
