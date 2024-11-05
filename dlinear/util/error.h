/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Utilities that verify assumptions made by the program and aborts
 * the program if those assumptions are not true.
 *
 * If NDEBUG is defined, most of the macro do nothing and give no explanation.
 * It makes the program faster, but less useful for debugging.
 */
#pragma once

#include <fmt/core.h>

#include <stdexcept>

#ifdef NDEBUG

#define DLINEAR_ASSERT(condition, msg) ((void)0)
#define DLINEAR_ASSERT_FMT(condition, msg, ...) ((void)0)
#define DLINEAR_UNREACHABLE() std::terminate()
#define DLINEAR_RUNTIME_ERROR(msg) throw std::runtime_error(msg)
#define DLINEAR_RUNTIME_ERROR_FMT(msg, ...) throw std::runtime_error(msg)
#define DLINEAR_OUT_OF_RANGE(msg) throw std::out_of_range(msg)
#define DLINEAR_OUT_OF_RANGE_FMT(msg, ...) throw std::out_of_range(msg)
#define DLINEAR_INVALID_ARGUMENT(argument, actual) throw std::runtime_error(argument)
#define DLINEAR_INVALID_ARGUMENT_EXPECTED(argument, actual, expected) \
  throw std::invalid_argument(                                        \
      fmt::format("Invalid argument for {}: received '{}', expected '{}'", argument, actual, expected))

#else

#include "dlinear/util/logging.h"

#define DLINEAR_ASSERT(condition, message)                                                                 \
  do {                                                                                                     \
    if (!(condition)) {                                                                                    \
      DLINEAR_CRITICAL_FMT("Assertion `{}` failed in {}:{}: {}", #condition, __FILE__, __LINE__, message); \
      std::terminate();                                                                                    \
    }                                                                                                      \
  } while (false)

#define DLINEAR_ASSERT_FMT(condition, message, ...)                                           \
  do {                                                                                        \
    if (!(condition)) {                                                                       \
      DLINEAR_CRITICAL_FMT("Assertion `{}` failed in {}:{}", #condition, __FILE__, __LINE__); \
      DLINEAR_CRITICAL_FMT(message, __VA_ARGS__);                                             \
      std::terminate();                                                                       \
    }                                                                                         \
  } while (false)

#define DLINEAR_UNREACHABLE()                                                   \
  do {                                                                          \
    DLINEAR_CRITICAL_FMT("{}:{} Should not be reachable.", __FILE__, __LINE__); \
    std::terminate();                                                           \
  } while (false)

#define DLINEAR_RUNTIME_ERROR(msg) \
  do {                             \
    DLINEAR_CRITICAL(msg);         \
    throw std::runtime_error(msg); \
  } while (false)

#define DLINEAR_RUNTIME_ERROR_FMT(msg, ...)                  \
  do {                                                       \
    DLINEAR_CRITICAL_FMT(msg, __VA_ARGS__);                  \
    throw std::runtime_error(fmt::format(msg, __VA_ARGS__)); \
  } while (false)

#define DLINEAR_OUT_OF_RANGE(msg) \
  do {                            \
    DLINEAR_CRITICAL(msg);        \
    throw std::out_of_range(msg); \
  } while (false)

#define DLINEAR_OUT_OF_RANGE_FMT(msg, ...)                  \
  do {                                                      \
    DLINEAR_CRITICAL_FMT(msg, __VA_ARGS__);                 \
    throw std::out_of_range(fmt::format(msg, __VA_ARGS__)); \
  } while (false)

#define DLINEAR_INVALID_ARGUMENT(argument, actual) \
  throw std::invalid_argument(fmt::format("Invalid argument for {}: {}", argument, actual))

#define DLINEAR_INVALID_ARGUMENT_EXPECTED(argument, actual, expected) \
  throw std::invalid_argument(                                        \
      fmt::format("Invalid argument for {}: received '{}', expected '{}'", argument, actual, expected))

#endif  // NDEBUG
