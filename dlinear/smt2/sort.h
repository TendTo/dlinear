/**
 * @file sort.h
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 * @brief Sort of a term.
 *
 * Indicates the type of a term.
 */
#ifndef DLINEAR_SMT2_SORT_H_
#define DLINEAR_SMT2_SORT_H_

#include <ostream>
#include <string>

#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/exception.h"

namespace dlinear {

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

}  // namespace dlinear

#endif  // DLINEAR_SMT2_SORT_H_
