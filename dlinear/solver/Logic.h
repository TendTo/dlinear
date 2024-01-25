/**
 * @file Logic.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Describes the logic of the SMT2 file using an enum class.
 *
 * dlinear supports only QL_LRA logic for now.
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
