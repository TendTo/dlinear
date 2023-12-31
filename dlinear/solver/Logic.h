/**
 * @file logic.h
 * @author dlinear
 * @date 13 Aug 2023
 * @copyright 2023 dlinear
 * @brief Describes the logic of the SMT2 file using an enum class.
 *
 * Dlinear supports either QL_LRA or QF_LIA logic.
 */
#pragma once

#include <ostream>
#include <string>

namespace dlinear {

enum class Logic {
  QF_NRA,      ///< Quantifier free non-linear real arithmetic
  QF_NRA_ODE,  ///< Quantifier free non-linear real arithmetic with ODEs
  QF_LRA,      ///< Quantifier free linear real arithmetic
  QF_RDL,      ///< Quantifier free real difference logic
  QF_LIA,      ///< Quantifier free linear integer arithmetic
};

Logic parseLogic(const std::string &s);
std::ostream &operator<<(std::ostream &os, const Logic &logic);

}  // namespace dlinear
