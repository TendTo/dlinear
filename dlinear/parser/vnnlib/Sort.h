/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Sort enum.
 */
#pragma once

#include <ostream>
#include <string>

#include "dlinear/symbolic/literal.h"

namespace dlinear::vnnlib {

/** Sort of a term. */
enum class Sort {
  Binary,  ///< Binary sort.
  Bool,    ///< Boolean sort.
  Int,     ///< Integer sort.
  Real,    ///< Real sort.
};

/**
 * Parse a string to a sort.
 * @param s string to parse
 * @return sort parsed from @p s
 */
Sort ParseSort(const std::string &s);
/**
 * Convert a sort to a variable type.
 *
 * The conversion is as follows:
 * - Binary -> BINARY
 * - Bool -> BOOLEAN
 * - Int -> INTEGER
 * - Real -> CONTINUOUS
 * @param sort sort to convert
 * @return variable type corresponding to @p sort
 */
Variable::Type SortToType(Sort sort);

std::ostream &operator<<(std::ostream &os, const Sort &sort);

}  // namespace dlinear::vnnlib

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::vnnlib::Sort)

#endif
