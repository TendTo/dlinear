/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Logging macros.
 * Allows logging with different verbosity levels using spdlog.
 *
 * The verbosity level is set with the -V flag.
 * The verbosity level is an integer between 0 and 5 and it increases with each -V flag.
 * It can be reduced with the -q flag.
 * It starts at 2 (warning).
 */
#pragma once

#ifndef NLOG

#include <fmt/core.h>     // IWYU pragma: export
#include <fmt/ostream.h>  // IWYU pragma: export
#include <fmt/ranges.h>   // IWYU pragma: export
#include <spdlog/logger.h>

#include <memory>

namespace dlinear {

enum class LoggerType { OUT, ERR };

std::shared_ptr<spdlog::logger> get_logger(LoggerType logger_type);  // NOLINT

}  // namespace dlinear

#define OSTREAM_FORMATTER(type) \
  template <>                   \
  struct fmt::formatter<type> : ostream_formatter {};
#define DLINEAR_FORMAT(message, ...) fmt::format(message, __VA_ARGS__)

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
#define DLINEAR_TRACE_FMT(msg, ...) ::dlinear::get_logger(::dlinear::LoggerType::OUT)->trace(msg, __VA_ARGS__)
#define DLINEAR_DEBUG(msg) ::dlinear::get_logger(::dlinear::LoggerType::OUT)->debug(msg)
#define DLINEAR_DEBUG_FMT(msg, ...) ::dlinear::get_logger(::dlinear::LoggerType::OUT)->debug(msg, __VA_ARGS__)
#define DLINEAR_INFO(msg) ::dlinear::get_logger(::dlinear::LoggerType::OUT)->info(msg)
#define DLINEAR_INFO_FMT(msg, ...) ::dlinear::get_logger(::dlinear::LoggerType::OUT)->info(msg, __VA_ARGS__)
#define DLINEAR_WARN(msg) ::dlinear::get_logger(::dlinear::LoggerType::ERR)->warn(msg)
#define DLINEAR_WARN_FMT(msg, ...) ::dlinear::get_logger(::dlinear::LoggerType::ERR)->warn(msg, __VA_ARGS__)
#define DLINEAR_ERROR(msg) ::dlinear::get_logger(::dlinear::LoggerType::ERR)->error(msg)
#define DLINEAR_ERROR_FMT(msg, ...) ::dlinear::get_logger(::dlinear::LoggerType::ERR)->error(msg, __VA_ARGS__)
#define DLINEAR_CRITICAL(msg) ::dlinear::get_logger(::dlinear::LoggerType::ERR)->critical(msg)
#define DLINEAR_CRITICAL_FMT(msg, ...) ::dlinear::get_logger(::dlinear::LoggerType::ERR)->critical(msg, __VA_ARGS__)
#define DLINEAR_INFO_ENABLED (::dlinear::get_logger(::dlinear::LoggerType::OUT)->should_log(spdlog::level::info))
#define DLINEAR_TRACE_ENABLED (::dlinear::get_logger(::dlinear::LoggerType::OUT)->should_log(spdlog::level::trace))

#ifndef NDEBUG

#include <sstream>
#include <thread>

#define DLINEAR_DEV(msg)                                                                                        \
  do {                                                                                                          \
    if (::dlinear::get_logger(::dlinear::LoggerType::ERR)->should_log(spdlog::level::err))                      \
      fmt::println("[{:%Y-%m-%d %H:%M:%S}] [\033[1m\033[35mDEV\033[0m] [thread {}] " msg "",                    \
                   std::chrono::system_clock::now(), std::hash<std::thread::id>{}(std::this_thread::get_id())); \
    std::cout << std::flush;                                                                                    \
  } while (0)
#define DLINEAR_DEV_FMT(msg, ...)                                                                              \
  do {                                                                                                         \
    if (::dlinear::get_logger(::dlinear::LoggerType::ERR)->should_log(spdlog::level::err))                     \
      fmt::println("[{:%Y-%m-%d %H:%M:%S}] [\033[1m\033[35mDEV\033[0m] [thread {}] " msg "",                   \
                   std::chrono::system_clock::now(), std::hash<std::thread::id>{}(std::this_thread::get_id()), \
                   __VA_ARGS__);                                                                               \
    std::cout << std::flush;                                                                                   \
  } while (0)

#define DLINEAR_DEV_TRACE(msg) DLINEAR_DEV(msg)
#define DLINEAR_DEV_TRACE_FMT(msg, ...) DLINEAR_DEV_FMT(msg, __VA_ARGS__)
#define DLINEAR_DEV_DEBUG(msg) DLINEAR_DEV(msg)
#define DLINEAR_DEV_DEBUG_FMT(msg, ...) DLINEAR_DEV_FMT(msg, __VA_ARGS__)
#else
#define DLINEAR_DEV(msg) void(0)
#define DLINEAR_DEV_FMT(msg, ...) void(0)
#define DLINEAR_DEV_TRACE(msg) DLINEAR_TRACE(msg)
#define DLINEAR_DEV_TRACE_FMT(msg, ...) DLINEAR_TRACE_FMT(msg, __VA_ARGS__)
#define DLINEAR_DEV_DEBUG(msg) DLINEAR_DEBUG(msg)
#define DLINEAR_DEV_DEBUG_FMT(msg, ...) DLINEAR_DEBUG_FMT(msg, __VA_ARGS__)
#endif

#else

#define OSTREAM_FORMATTER(type)
#define DLINEAR_FORMAT(message, ...) fmt::format(message, __VA_ARGS__)
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
#define DLINEAR_DEV(msg) void(0)
#define DLINEAR_DEV_FMT(msg, ...) void(0)
#define DLINEAR_DEV_TRACE(msg) void(0)
#define DLINEAR_DEV_TRACE_FMT(msg, ...) void(0)
#define DLINEAR_DEV_DEBUG(msg) void(0)
#define DLINEAR_DEV_DEBUG_FMT(msg, ...) void(0)

#endif
