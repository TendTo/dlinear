#include <iostream>
#include "dlinear/util/ArgParser.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/assert.h"
#include "dlinear/util/logging.h"


using dlinear::ArgParser;
using dlinear::Config;


int main(int argc, const char *argv[]) {
    ArgParser parser{};
    parser.parse(argc, argv);
    Config c = parser.toConfig();
    std::cout << parser << std::endl;
    std::cout << c << std::endl;
}
