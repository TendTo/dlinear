#include "Stats.h"

namespace dlinear {
    template<typename T>
    void Stats::increase(atomic<T> *v) {
        if (enabled_) {
            atomic_fetch_add_explicit(v, 1, memory_order_relaxed);
        }
    }
} // dlinear