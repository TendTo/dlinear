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
 * @tparam T type to check
 * @tparam U any number of types to check against
 */
template <typename T, typename... U>
concept IsAnyOf = (std::same_as<T, U> || ...);

/**
 * Check if the type T is not any of the types U
 * @tparam T type to check
 * @tparam U any number of types to check against
 */
template <typename T, typename... U>
concept IsNotAnyOf = !IsAnyOf<T, U...>;

/**
 * Check if the type T supports the arithmetic operations +, -, *, /
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
 * @tparam T type to check
 */
template <class T>
concept Numeric = std::totally_ordered<T> && Arithmetic<T>;

}  // namespace dlinear
