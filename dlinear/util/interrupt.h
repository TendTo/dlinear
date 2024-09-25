/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 * Interrupt handler used by pydlinear to handle SIGINT.
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
