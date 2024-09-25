/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * Describes the logic of the SMT2 file using an enum class.
 *
 * dlinear supports only QL_LRA logic for now.
 */
#pragma once

#include <ostream>
#include <string>

namespace dlinear {

/** Describe the logic the SMT2 file is using. */
enum class Logic {
  QF_NRA,      ///< Quantifier free non-linear real arithmetic
  QF_NRA_ODE,  ///< Quantifier free non-linear real arithmetic with ODEs
  QF_LRA,      ///< Quantifier free linear real arithmetic
  QF_RDL,      ///< Quantifier free real difference logic
  QF_LIA,      ///< Quantifier free linear integer arithmetic
  LRA,         ///< Linear real arithmetic
};

/**
 * Parse the logic from a string.
 * @param s string to parse
 * @return corresponding logic
 */
Logic parseLogic(const std::string &s);
std::ostream &operator<<(std::ostream &os, const Logic &logic);

}  // namespace dlinear

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::Logic)

#endif
