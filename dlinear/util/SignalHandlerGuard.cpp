/**
 * @file SignalHandlerGuard.cpp
 * @author dlinear
 * @version 0.1
 * @date 14 Aug 2023
 * @copyright 2023 dlinear
 */
#include "SignalHandlerGuard.h"

#include <iostream>
#include <stdexcept>

namespace dlinear {

using std::atomic_bool;
using std::runtime_error;

SignalHandlerGuard::SignalHandlerGuard(const int sig, handler_t handler, volatile atomic_bool* flag)
    : sig_{sig}, flag_{flag}, old_action_{} {
  // Register the new handler and save the current one.
  struct sigaction new_action {};
  new_action.sa_handler = handler;
  sigemptyset(&new_action.sa_mask);
  new_action.sa_flags = SA_RESTART;
  const int result = sigaction(sig_, &new_action, &old_action_);
  if (result != 0) {
    throw runtime_error("Failed to register the signal handler.");
  }
}

SignalHandlerGuard::~SignalHandlerGuard() {
  // Restore the old signal handler
  sigaction(sig_, &old_action_, nullptr);
  if (*flag_) {
    *(flag_) = false;
  }
}
}  // namespace dlinear
