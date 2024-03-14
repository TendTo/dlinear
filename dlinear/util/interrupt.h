/**
 * @file interrupt.h
 * @author dlinear
 * @date 14 Aug 2023
 * @copyright 2023 dlinear
 * @brief Interrupt handler used by pydlinear to handle SIGINT.
 */
#pragma once

#include <atomic>

namespace dlinear {

extern volatile std::atomic_bool g_interrupted;  ///< Flag to indicate an interrupt (SIGINT) is received.

/**
 * Signal handler for SIGINT.
 * Set the @ref g_interrupted flag to true.
 */
void interrupt_handler(int);

}  // namespace dlinear
