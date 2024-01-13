//
// Created by c3054737 on 12/01/24.
//
#pragma once

#include <ostream>
#include <string>

namespace dlinear {

enum class LpResult {
  LP_NO_RESULT,
  LP_UNSOLVED,
  LP_INFEASIBLE,
  LP_UNBOUNDED,
  LP_OPTIMAL,
  LP_DELTA_OPTIMAL,
};

LpResult parseLpResult(int res);
std::ostream &operator<<(std::ostream &os, const LpResult &lp_result);

}  // namespace dlinear
