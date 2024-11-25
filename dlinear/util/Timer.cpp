/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */

#include "Timer.h"

#include <sys/resource.h>

#include <stdexcept>

#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

template <class T>
TimerBase<T>::TimerBase() : last_start_{now()} {}

template <class T>
void TimerBase<T>::Start() {
  DLINEAR_TRACE("TimerBase::Start");
  last_start_ = now();
  elapsed_ = duration{0};
  running_ = true;
}

template <class T>
void TimerBase<T>::Pause() {
  if (running_) {
    running_ = false;
    elapsed_ += (now() - last_start_);
  }
}

template <class T>
void TimerBase<T>::Resume() {
  if (!running_) {
    last_start_ = now();
    running_ = true;
  }
}

template <class T>
bool TimerBase<T>::is_running() const {
  return running_;
}

template <class T>
typename TimerBase<T>::duration TimerBase<T>::elapsed() const {
  DLINEAR_TRACE("TimerBase::duration");
  return running_ ? elapsed_ + (now() - last_start_) : elapsed_;
}

template <class T>
std::chrono::duration<double>::rep TimerBase<T>::seconds() const {
  DLINEAR_TRACE("TimerBase::seconds");
  return std::chrono::duration_cast<std::chrono::duration<double>>(elapsed()).count();
}

user_clock::time_point user_clock::now() {
  DLINEAR_TRACE("user_clock::now");
  struct rusage usage{};
  if (0 != getrusage(RUSAGE_SELF, &usage)) throw DlinearException("Failed to get current resource usage (getrusage)");
  return time_point(duration(static_cast<uint64_t>(usage.ru_utime.tv_sec) * std::micro::den + static_cast<uint64_t>(usage.ru_utime.tv_usec)));
}

// Explicit instantiations
template class TimerBase<chosen_steady_clock>;
template class TimerBase<user_clock>;

TimerGuard::TimerGuard(Timer *const timer, const bool enabled, const bool start_timer)
    : timer_{timer}, enabled_{enabled && timer_ != nullptr} {
  if (enabled_ && start_timer) timer_->Resume();
}

TimerGuard::~TimerGuard() {
  if (enabled_) timer_->Pause();
}

void TimerGuard::Pause() {
  if (enabled_) timer_->Pause();
}

void TimerGuard::Resume() {
  if (enabled_) timer_->Resume();
}

}  // namespace dlinear
