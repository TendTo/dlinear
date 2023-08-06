#ifndef DLINEAR5_STATS_H
#define DLINEAR5_STATS_H

#include <atomic>

using std::atomic;
using std::atomic_fetch_add_explicit;
using std::memory_order_relaxed;

namespace dlinear {

    class Stats {
    private:
        const bool enabled_{false};

    protected:
        template<typename T>
        void increase(atomic<T> *v);

    public:
        explicit Stats(bool enabled) : enabled_{enabled} {}

        Stats(const Stats &) = default;

        Stats(Stats &&) = default;

        Stats &operator=(const Stats &) = delete;

        Stats &operator=(Stats &&) = delete;

        virtual ~Stats() = default;

        /// \brief Returns whether the stats is enabled.
        /// \return true if the stats is enabled, false otherwise.
        [[nodiscard]] bool enabled() const { return enabled_; }
    };

} // dlinear

#endif //DLINEAR5_STATS_H
