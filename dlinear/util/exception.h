/**
 * @file assert.h
 * @author tend
 * @date 07 Aug 2023
 * @copyright 2023 tend
 * Assert macro. Assert that the condition is true, otherwise abort.
 *
 * If NDEBUG is defined, the assert macro does nothing.
 */
#ifndef DLINEAR5_ASSERT_H
#define DLINEAR5_ASSERT_H

#ifdef NDEBUG
#define DLINEAR_ASSERT(condition, msg) ((void)0)
#else

#include <cassert>
#include <cstdlib>
#include <stdexcept>
#include "dlinear/util/logging.h"
#include <spdlog/fmt/fmt.h>

using std::abort;
using std::runtime_error;
using std::invalid_argument;

#define DLINEAR_ASSERT(condition, msg) assert(condition &&msg)
#endif

#define DLINEAR_UNREACHABLE()                                                   \
  do {                                                                          \
    DLINEAR_CRITICAL_FMT("{}:{} Should not be reachable.", __FILE__, __LINE__); \
    abort();                                                                    \
  } while (false)

#define DLINEAR_RUNTIME_ERROR(msg) \
  do {                             \
    DLINEAR_CRITICAL(msg);         \
    throw runtime_error(msg);      \
  } while (false)

#define DLINEAR_RUNTIME_ERROR_FMT(msg, ...)               \
  do {                                                    \
    DLINEAR_CRITICAL_FMT(msg, ##__VA_ARGS__);             \
    throw runtime_error(fmt::format(msg, ##__VA_ARGS__)); \
  } while (false)

#define DLINEAR_INVALID_ARGUMENT(argument, actual) throw invalid_argument(fmt::format("Invalid argument for {} - {}\n", argument, actual))

#endif // DLINEAR5_ASSERT_H
