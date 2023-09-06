#ifndef DLINEAR_UTIL_INTERRUPT_H_
#define DLINEAR_UTIL_INTERRUPT_H_

#include <atomic>

namespace dlinear {

extern volatile std::atomic_bool g_interrupted;  ///< Flag to indicate an interrupt (SIGINT) is received.

/**
 * Signal handler for SIGINT.
 * Set the @ref g_interrupted flag to true.
 * @param sig signal number (ignored)
 */
void interrupt_handler(int);

}  // namespace dlinear

#endif  // DLINEAR_UTIL_INTERRUPT_H_
