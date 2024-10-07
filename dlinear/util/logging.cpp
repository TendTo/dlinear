/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */

#include "logging.h"

#ifndef NLOG

#include <spdlog/common.h>
#include <spdlog/sinks/stdout_color_sinks.h>
#include <spdlog/spdlog.h>

namespace dlinear {

std::shared_ptr<spdlog::logger> get_logger(LoggerType logger_type) {
  // Checks if there exists a logger with the name. If it exists, return it.
  const char *logger_name = logger_type == LoggerType::OUT ? "dlinear_out" : "dlinear_err";
  std::shared_ptr<spdlog::logger> logger{spdlog::get(logger_name)};
  if (logger) return logger;

  // Create and return a new logger.
  logger = logger_type == LoggerType::OUT ? spdlog::stdout_color_mt(logger_name) : spdlog::stderr_color_mt(logger_name);

  // Turn it off by default so that external programs using dReal as a library do not see internal loggings.
  logger->set_level(spdlog::level::off);

  // Set format.
  logger->set_pattern("[%Y-%m-%d %H:%M:%S.%e] [%^%l%$] [thread %t] %v");

  return logger;
}

}  // namespace dlinear

#else

#endif  // NLOG
