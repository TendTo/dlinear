/**
 * @file math.h
 * @author dlinear
 * @date 14 Aug 2023
 * @copyright 2023 dlinear
 * @brief Math utilities
 */

#ifndef DLINEAR5_DLINEAR_UTIL_MATH_H_
#define DLINEAR5_DLINEAR_UTIL_MATH_H_

#include "dlinear/libs/gmp.h"

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
 * @throws std::runtime_error if this conversion result in a loss of precision.
 * @param v value to convert
 * @return converted value
 */
int convert_int64_to_int(int64_t v);

/**
 * Convert @p v of int64_t to double.
 * @throws std::runtime_error if this conversion result in a loss of precision.
 * @param v value to convert
 * @return converted value
 */
double convert_int64_to_double(int64_t v);

/**
 * Convert @p v of int64_t to rational.
 * @param v value to convert
 * @return converted value
 */
mpq_class convert_int64_to_rational(int64_t v);

}  // namespace dlinear

#endif //DLINEAR5_DLINEAR_UTIL_MATH_H_
