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
#pragma once

#ifndef NLOG

#include <spdlog/spdlog.h>
// Enable formatting with the override of operator<< for user-defined types.
// Must be included after spdlog.h.
#include <fmt/ostream.h>
#include <fmt/ranges.h>

#include <memory>

namespace dlinear {

enum class LoggerType { OUT, ERR };

std::shared_ptr<spdlog::logger> get_logger(LoggerType logger_type);  // NOLINT

}  // namespace dlinear

#define OSTREAM_FORMATTER(type) \
  template <>                   \
  struct fmt::formatter<type> : ostream_formatter {};

#define DLINEAR_VERBOSITY_TO_LOG_LEVEL(verbosity)                      \
  ((verbosity) == 0                                                    \
       ? spdlog::level::critical                                       \
       : ((verbosity) == 1                                             \
              ? spdlog::level::err                                     \
              : ((verbosity) == 2                                      \
                     ? spdlog::level::warn                             \
                     : ((verbosity) == 3                               \
                            ? spdlog::level::info                      \
                            : ((verbosity) == 4 ? spdlog::level::debug \
                                                : ((verbosity) == 5 ? spdlog::level::trace : spdlog::level::off))))))
#define DLINEAR_LOG_INIT_VERBOSITY(verbosity) DLINEAR_LOG_INIT_LEVEL(DLINEAR_VERBOSITY_TO_LOG_LEVEL(verbosity))
#define DLINEAR_LOG_INIT_LEVEL(level)                                    \
  do {                                                                   \
    ::dlinear::get_logger(::dlinear::LoggerType::OUT)->set_level(level); \
    ::dlinear::get_logger(::dlinear::LoggerType::ERR)->set_level(level); \
  } while (0)
#define DLINEAR_TRACE(msg) ::dlinear::get_logger(::dlinear::LoggerType::OUT)->trace(msg)
#define DLINEAR_TRACE_FMT(msg, ...) ::dlinear::get_logger(::dlinear::LoggerType::OUT)->trace(msg, ##__VA_ARGS__)
#define DLINEAR_DEBUG(msg) ::dlinear::get_logger(::dlinear::LoggerType::OUT)->debug(msg)
#define DLINEAR_DEBUG_FMT(msg, ...) ::dlinear::get_logger(::dlinear::LoggerType::OUT)->debug(msg, ##__VA_ARGS__)
#define DLINEAR_INFO(msg) ::dlinear::get_logger(::dlinear::LoggerType::OUT)->info(msg)
#define DLINEAR_INFO_FMT(msg, ...) ::dlinear::get_logger(::dlinear::LoggerType::OUT)->info(msg, ##__VA_ARGS__)
#define DLINEAR_WARN(msg) ::dlinear::get_logger(::dlinear::LoggerType::ERR)->warn(msg)
#define DLINEAR_WARN_FMT(msg, ...) ::dlinear::get_logger(::dlinear::LoggerType::ERR)->warn(msg, ##__VA_ARGS__)
#define DLINEAR_ERROR(msg) ::dlinear::get_logger(::dlinear::LoggerType::ERR)->error(msg)
#define DLINEAR_ERROR_FMT(msg, ...) ::dlinear::get_logger(::dlinear::LoggerType::ERR)->error(msg, ##__VA_ARGS__)
#define DLINEAR_CRITICAL(msg) ::dlinear::get_logger(::dlinear::LoggerType::ERR)->critical(msg)
#define DLINEAR_CRITICAL_FMT(msg, ...) ::dlinear::get_logger(::dlinear::LoggerType::ERR)->critical(msg, ##__VA_ARGS__)
#define DLINEAR_INFO_ENABLED (::dlinear::get_logger(::dlinear::LoggerType::OUT)->should_log(spdlog::level::info))
#define DLINEAR_TRACE_ENABLED (::dlinear::get_logger(::dlinear::LoggerType::OUT)->should_log(spdlog::level::trace))

#else

#define OSTREAM_FORMATTER(type)
#define DLINEAR_VERBOSITY_TO_LOG_LEVEL(verbosity) 0
#define DLINEAR_LOG_INIT_LEVEL(level) void(0)
#define DLINEAR_LOG_INIT_VERBOSITY(verbosity) void(0)
#define DLINEAR_TRACE(msg) void(0)
#define DLINEAR_TRACE_FMT(msg, ...) void(0)
#define DLINEAR_DEBUG(msg) void(0)
#define DLINEAR_DEBUG_FMT(msg, ...) void(0)
#define DLINEAR_INFO(msg) void(0)
#define DLINEAR_INFO_FMT(msg, ...) void(0)
#define DLINEAR_WARN(msg) void(0)
#define DLINEAR_WARN_FMT(msg, ...) void(0)
#define DLINEAR_ERROR(msg) void(0)
#define DLINEAR_ERROR_FMT(msg, ...) void(0)
#define DLINEAR_CRITICAL(msg) void(0)
#define DLINEAR_CRITICAL_FMT(msg, ...) void(0)
#define DLINEAR_INFO_ENABLED false
#define DLINEAR_TRACE_ENABLED false

#endif
