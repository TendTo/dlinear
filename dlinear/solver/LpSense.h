//
// Created by c3054737 on 16/01/24.
//
#pragma once

#include <ostream>

namespace dlinear {

enum class LpSense {
  GT,  ///< Greater than
  GE,  ///< Greater than or equal to
  EQ,  ///< Equal to
  NQ,  ///< Not equal to
  LE,  ///< Less than or equal to
  LT,  ///< Less than
  IN,  ///< Inactive
};

inline constexpr LpSense parseLpSense(char sense);
inline constexpr char toChar(LpSense sense);
inline constexpr LpSense operator!(LpSense sense);
inline constexpr double epsilon_multiplier(LpSense sense);
std::ostream &operator<<(std::ostream &os, const LpSense &lp_result);

}  // namespace dlinear
