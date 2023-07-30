#include <iostream>
#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/assert.h"
#include "dlinear/util/logging.h"


using dlinear::ArgParser;
using dlinear::Config;


int main([[maybe_unused]]int argc, [[maybe_unused]] const char *argv[]) {
    ArgParser parser{};
    parser.parse(argc, argv);
    DLINEAR_ASSERT(argc < 10, "argc must be at least 10");
    DLINEAR_CRITICAL("argc must be at least {}", 10);
    DLINEAR_ERROR("argc must be at least {}", 10);
    DLINEAR_WARN("argc must be at least {}", 10);
    DLINEAR_INFO("argc must be at least {}", 10);
    DLINEAR_DEBUG("argc must be at least {}", 10);
    DLINEAR_TRACE("argc must be at least {}", 10);
    Config c = parser.toConfig();
    std::cout << parser << std::endl;
    std::cout << c << std::endl;
}
