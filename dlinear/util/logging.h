/**
 * @file logging.h
 * @author dlinear
 * @date 07 Aug 2023
 * @copyright 2023 dlinear
 * Logging macros.
 * Allows logging with different verbosity levels using spdlog.
 *
 * The verbosity level is set with the --verbosity flag.
 * The verbosity level is an integer between 0 and 5.
 * The higher the verbosity level, the more information is logged.
 * If another value is provided, the logging is turned off.
 */
#ifndef DLINEAR5_LOGGING_H
#define DLINEAR5_LOGGING_H

#include <spdlog/spdlog.h>
#include "spdlog/fmt/ostr.h"

namespace dlinear {

#define DLINEAR_VERBOSITY_TO_LOG_LEVEL(verbosity) \
    (verbosity == 0 ? spdlog::level::critical :   \
    (verbosity == 1 ? spdlog::level::err   :      \
    (verbosity == 2 ? spdlog::level::warn  :      \
    (verbosity == 3 ? spdlog::level::info  :      \
    (verbosity == 4 ? spdlog::level::debug :      \
    (verbosity == 5 ? spdlog::level::trace :      \
    spdlog::level::off))))))
#define DLINEAR_LOG_INIT(level) \
    do {                   \
        spdlog::set_level(level); \
        spdlog::set_pattern("[%Y-%m-%d %H:%M:%S.%e] [%^%l%$] [thread %t] %v"); \
    } \
    while (0)
#define DLINEAR_TRACE(msg) spdlog::trace(msg)
#define DLINEAR_TRACE_FMT(msg, ...) spdlog::trace(msg, ##__VA_ARGS__)
#define DLINEAR_DEBUG(msg) spdlog::debug(msg)
#define DLINEAR_DEBUG_FMT(msg, ...) spdlog::debug(msg, ##__VA_ARGS__)
#define DLINEAR_INFO(msg) spdlog::info(msg)
#define DLINEAR_INFO_FMT(msg, ...) spdlog::info(msg, ##__VA_ARGS__)
#define DLINEAR_WARN(msg) spdlog::warn(msg)
#define DLINEAR_WARN_FMT(msg, ...) spdlog::warn(msg, ##__VA_ARGS__)
#define DLINEAR_ERROR(msg) spdlog::error(msg)
#define DLINEAR_ERROR_FMT(msg, ...) spdlog::error(msg, ##__VA_ARGS__)
#define DLINEAR_CRITICAL(msg) spdlog::critical(msg)
#define DLINEAR_CRITICAL_FMT(msg, ...) spdlog::critical(msg, ##__VA_ARGS__)

}  // namespace dlinear

#endif  // DLINEAR5_LOGGING_H
