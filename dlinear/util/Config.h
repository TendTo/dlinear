#ifndef DLINEAR5_CONFIG_H
#define DLINEAR5_CONFIG_H

#include <iostream>

using std::ostream;
using std::endl;

namespace dlinear {

    class Config {
    private:
        int verbosity_;
        double precision_;
        bool produceModels_;
        u_int32_t randomSeed_;

    public:
        Config() = default;

        [[nodiscard]] int getVerbosity() const { return verbosity_; }

        void setVerbosity(int verbosity) { verbosity_ = verbosity; }

        [[nodiscard]] double getPrecision() const { return precision_; }

        void setPrecision(double precision) { precision_ = precision; }

        [[nodiscard]] bool getProduceModels() const { return produceModels_; }

        void setProduceModels(bool produceModels) { produceModels_ = produceModels; }

        [[nodiscard]] u_int32_t getRandomSeed() const { return randomSeed_; }

        void setRandomSeed(u_int32_t randomSeed) { randomSeed_ = randomSeed; }

        friend ostream &operator<<(ostream &os, const Config &config);
    };

} // dlinear

#endif //DLINEAR5_CONFIG_H
