/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Column struct.
 */
#pragma once

#include <iosfwd>
#include <optional>

#include "dlinear/libs/libgmp.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear::mps {

/**
 * Data structure representing a column in the LP solver as it gets parsed from an MPS file.
 * Missing bounds are represented by `std::nullopt` and may have different meanings.
 * If any of the bounds is set, the variable is bounded from that direction.
 * A missing upper bound on a non-integer variable means that the variable is unbounded in the positive direction.
 * A missing upper bound on an integer variable means that the variable is bounded by 1.
 * Unless `is_infinite_ub_integer` is set to true, in which case the variable is unbounded in the positive direction.
 * A missing lower bound with @ref is_infinite_lb = false means that the variable is non-negative (@f$ x \geq 0 @f$).
 * On the other hand, if @ref is_infinite_lb = true, the variable is unbounded in the negative direction.
 */
struct Column {
  Column() = default;
  explicit Column(const Variable& _var, const bool _is_integer = false)
      : var{_var},
        lb{std::nullopt},
        ub{std::nullopt},
        is_integer{_is_integer},
        is_infinite_ub_integer{false},
        is_infinite_lb{false} {}
  Column(const Variable& _var, const mpq_class& _ub) : var{_var}, lb{std::nullopt}, ub{_ub}, is_infinite_lb{false} {}
  Column(const Variable& _var, const mpq_class& _lb, const mpq_class& _ub)
      : var{_var}, lb{_lb}, ub{_ub}, is_infinite_lb{false} {}
  const mpq_class* ComputeLb() const {
    static const mpq_class zero{0};
    return lb.has_value() ? &lb.value() : is_infinite_lb || ub.value_or(0) < 0 ? nullptr : &zero;
  }
  const mpq_class* ComputeUb() const {
    static const mpq_class one{1};
    return ub.has_value() ? &ub.value() : !is_integer || is_infinite_ub_integer ? nullptr : &one;
  }
  Variable var;                        ///< Variable.
  std::optional<mpq_class> lb;         ///< Lower bound.
  std::optional<mpq_class> ub;         ///< Upper bound.
  bool is_integer{false};              ///< Indicates if the variable is integer. The default upper bound is 1.
  bool is_infinite_ub_integer{false};  ///< Indicates if the upper bound of an integer variable has changed to infinity.
  bool is_infinite_lb{false};          ///< Indicates if the lower bound is negative infinity.
};

std::ostream& operator<<(std::ostream& os, const Column& column);

}  // namespace dlinear::mps

#ifdef DLINEAR_INCLUDE_FMT

#include "dlinear/util/logging.h"

OSTREAM_FORMATTER(dlinear::mps::Column)

#endif
