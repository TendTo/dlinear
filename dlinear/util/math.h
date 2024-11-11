/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @copyright 2017 Toyota Research Institute (dreal4)
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
bool IsInteger(double v);
/**
 * Check if @p v is represented by `int`.
 * @param v value to check
 * @return whether @p v is represented by `int`
 */
bool IsInteger(const mpq_class &v);

/**
 * Convert @p v of int64_t to int.
 * @throw std::runtime_error if this conversion result in a loss of precision.
 * @param v value to convert
 * @return converted value
 */
int ConvertInt64ToInt(std::int64_t v);

/**
 * Convert @p v of int64_t to double.
 * @throw std::runtime_error if this conversion result in a loss of precision.
 * @param v value to convert
 * @return converted value
 */
double ConvertInt64ToDouble(std::int64_t v);

/**
 * Convert @p v of int64_t to rational.
 * @param v value to convert
 * @return converted value
 */
mpq_class ConvertInt64ToRational(std::int64_t v);

}  // namespace dlinear
