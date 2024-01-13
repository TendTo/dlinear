//
// Created by c3054737 on 12/01/24.
//
#pragma once

#include <ostream>
#include <string>

namespace dlinear {

enum class SatResult {
  SAT_NO_RESULT,
  SAT_UNSOLVED,
  SAT_UNSATISFIABLE,
  SAT_SATISFIABLE,
  SAT_DELTA_SATISFIABLE,
};

std::ostream &operator<<(std::ostream &os, const SatResult &sat_result);

}  // namespace dlinear
