#include "interrupt.h"

namespace dlinear {

volatile std::atomic_bool g_interrupted{false};

void interrupt_handler(int) { g_interrupted = true; }

}  // namespace dlinear
