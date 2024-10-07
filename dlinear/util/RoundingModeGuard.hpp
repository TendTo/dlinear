/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * RoundingModeGuard class.
 */
#pragma once

#include <cfenv>

namespace dlinear {

class RoundingModeGuard {
 public:
  /** Save the current rounding-mode and switch to @p new_round. */
  explicit RoundingModeGuard(int new_round) : round_mode_{fegetround()} { fesetround(new_round); }

  RoundingModeGuard(const RoundingModeGuard &) = delete;
  RoundingModeGuard(RoundingModeGuard &&) = delete;
  RoundingModeGuard &operator=(const RoundingModeGuard &) = delete;
  RoundingModeGuard &operator=(RoundingModeGuard &&) = delete;

  /** Destructor. Restore the saved rounding-mode. */
  ~RoundingModeGuard() { fesetround(round_mode_); }

 private:
  const int round_mode_{};  ///< Saved rounding-mode stored at construction time, to be restored at destruction time.
};

}  // namespace dlinear
