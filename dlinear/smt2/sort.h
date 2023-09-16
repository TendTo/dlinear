/**
 * @file sort.h
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 * @brief Sort of a term.
 *
 * Indicates the type of a term.
 */
#pragma once

#include <ostream>
#include <string>

#include "dlinear/symbolic/symbolic.h"

namespace dlinear::smt2 {

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

}  // namespace dlinear::smt2
