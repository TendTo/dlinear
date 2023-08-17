/**
 * @file assert.h
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 * @brief Utilities that verify assumptions made by the program and aborts
 * the program if those assumptions are not true.
 *
 * If NDEBUG is defined, most of the macro do nothing and give no explanation.
 * It makes the program faster, but less useful for debugging.
 */
#ifndef DLINEAR5_ASSERT_H
#define DLINEAR5_ASSERT_H

#include <stdexcept>

#ifdef NDEBUG

#define DLINEAR_ASSERT(condition, msg) ((void)0)
#define DLINEAR_UNREACHABLE() terminate()
#define DLINEAR_RUNTIME_ERROR(msg) throw runtime_error(msg)
#define DLINEAR_RUNTIME_ERROR_FMT(msg, ...) throw runtime_error()
#define DLINEAR_INVALID_ARGUMENT(argument, actual) throw runtime_error()

#else

#include "dlinear/util/logging.h"
#include <spdlog/fmt/fmt.h>

#define DLINEAR_ASSERT(condition, message)                                                                        \
    do {                                                                                                          \
        if (!(condition)) {                                                                                       \
            DLINEAR_CRITICAL_FMT("Assertion `{}` failed in {}:{}: {}", #condition, __FILE__, __LINE__, message);  \
            std::terminate();                                                                                     \
        }                                                                                                         \
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

#define DLINEAR_RUNTIME_ERROR_FMT(msg, ...)                     \
  do {                                                          \
    DLINEAR_CRITICAL_FMT(msg, ##__VA_ARGS__);                   \
    throw std::runtime_error(fmt::format(msg, ##__VA_ARGS__));  \
  } while (false)

#define DLINEAR_INVALID_ARGUMENT(argument, actual) throw std::invalid_argument(fmt::format("Invalid argument for {} - {}\n", argument, actual))

#endif // NDEBUG

#endif // DLINEAR5_ASSERT_H
