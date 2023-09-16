/**
 * @file interrupt.cpp
 * @author dlinear
 * @date 14 Aug 2023
 * @copyright 2023 dlinear
 */
#include "interrupt.h"

namespace dlinear {

volatile std::atomic_bool g_interrupted{false};

void interrupt_handler(int) { g_interrupted = true; }

}  // namespace dlinear
