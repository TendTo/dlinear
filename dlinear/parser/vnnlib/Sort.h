/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Sort of a term.
 *
 * Indicates the type of a term.
 */
#pragma once

#include <ostream>
#include <string>

#include "dlinear/symbolic/literal.h"

namespace dlinear::vnnlib {

// TODO(soonho): Extend this.
enum class Sort {
  Binary,
  Bool,
  Int,
  Real,
};

Sort ParseSort(const std::string &s);

std::ostream &operator<<(std::ostream &os, const Sort &sort);

Variable::Type SortToType(Sort sort);

}  // namespace dlinear::vnnlib

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::vnnlib::Sort)

#endif
