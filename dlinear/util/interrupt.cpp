/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "interrupt.h"

namespace dlinear {

volatile std::atomic_bool g_interrupted{false};

void interrupt_handler(int) { g_interrupted = true; }

}  // namespace dlinear
