/**
 * @file concepts.h
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * @brief Collection of concepts used in the dlinear library.
 *
 * Utility file that contains c++20 concepts used in the dlinear library
 * in order to make the code more readable and to provide better error messages.
 */
#pragma once

#include <concepts>

namespace dlinear {

/**
 * Check if the type T is any of the types U
 * @code
 * template <IsAnyOf<int, float, bool> T>
 * void foo(T t); // T can be either int, float or bool
 * @endcode
 * @tparam T type to check
 * @tparam U any number of types to check against
 */
template <typename T, typename... U>
concept IsAnyOf = (std::same_as<T, U> || ...);

/**
 * Check if the type T is not any of the types U
 * @code
 * template <IsNotAnyOf<int, float, bool> T>
 * void foo(T t); // T can be any type except int, float or bool
 * @endcode
 * @tparam T type to check
 * @tparam U any number of types to check against
 */
template <typename T, typename... U>
concept IsNotAnyOf = !IsAnyOf<T, U...>;

/**
 * Check if the type T supports the arithmetic operations +, -, *, /
 * @code
 * template <Arithmetic T>
 * void foo(T a, T b); // a and b can be added, subtracted, multiplied and divided with the corresponding operator
 * @endcode
 * @tparam T type to check
 */
template <class T>
concept Arithmetic = requires(T a, T b) {
  { a + b } -> std::convertible_to<T>;
  { a - b } -> std::convertible_to<T>;
  { a* b } -> std::convertible_to<T>;
  { a / b } -> std::convertible_to<T>;
};  // NOLINT(readability/braces) per C++ standard concept definition

/**
 * Check if the type T supports the arithmetic operations +, -, *, / and the comparison operators <, >, <=, >=
 * @code
 * template <Numeric T>
 * void foo(T a); // a can be added, subtracted, multiplied, divided and ordered with the corresponding operator
 * @endcode
 * @tparam T type to check
 */
template <class T>
concept Numeric = std::totally_ordered<T> && Arithmetic<T>;

}  // namespace dlinear
