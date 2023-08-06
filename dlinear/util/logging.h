#ifndef DLINEAR5_LOGGING_H
#define DLINEAR5_LOGGING_H

#include <spdlog/spdlog.h>

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
    while(0)
#define DLINEAR_TRACE(msg, ...) spdlog::trace(msg, ##__VA_ARGS__)
#define DLINEAR_DEBUG(msg, ...) spdlog::debug(msg, ##__VA_ARGS__)
#define DLINEAR_INFO(msg, ...) spdlog::info(msg, ##__VA_ARGS__)
#define DLINEAR_WARN(msg, ...) spdlog::warn(msg, ##__VA_ARGS__)
#define DLINEAR_ERROR(msg, ...) spdlog::error(msg, ##__VA_ARGS__)
#define DLINEAR_CRITICAL(msg, ...) spdlog::critical(msg, ##__VA_ARGS__)

} // dlinear

#endif //DLINEAR5_LOGGING_H
