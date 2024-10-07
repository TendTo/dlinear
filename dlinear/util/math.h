/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Math utilities.
 */
#pragma once

#include <cstdint>

#include "dlinear/libs/libgmp.h"

namespace dlinear {

/// Returns true if @p v is represented by `int`.
/**
 * Check if @p v is represented by `int`.
 * @param v value to check
 * @return whether @p v is represented by `int`
 */
bool is_integer(double v);
/**
 * Check if @p v is represented by `int`.
 * @param v value to check
 * @return whether @p v is represented by `int`
 */
bool is_integer(const mpq_class &v);

/**
 * Convert @p v of int64_t to int.
 * @throw std::runtime_error if this conversion result in a loss of precision.
 * @param v value to convert
 * @return converted value
 */
int convert_int64_to_int(std::int64_t v);

/**
 * Convert @p v of int64_t to double.
 * @throw std::runtime_error if this conversion result in a loss of precision.
 * @param v value to convert
 * @return converted value
 */
double convert_int64_to_double(std::int64_t v);

/**
 * Convert @p v of int64_t to rational.
 * @param v value to convert
 * @return converted value
 */
mpq_class convert_int64_to_rational(std::int64_t v);

}  // namespace dlinear
